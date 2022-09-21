// Copyright (c) 2022 Espresso Systems (espressosys.com)
// This file is part of the VeriZexe library.

// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version. This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
// details. You should have received a copy of the GNU General Public License along with this program. If not, see <https://www.gnu.org/licenses/>.

//! This module implements a DEX style private transaction protocol,
//! where there are three of transactions: mint, exchange and cancel.
//!
//! For general information on how such applications are implemented,
//! see the other examples.
//!
//! Application may vary in how they define the birth/death predicates.
//! In our case, we argue for the following knowledge:
//!
//! - a death predicate that checks:
//!     - the values are correctly committed via the `common_local_data`
//!
//! - a birth predicate that checks:
//!     - the values are correctly committed via the `common_local_data`
//!     - if mode is `mint`, there should only be dummy input notes
//!     - if mode is `mint`, there should onlyb be one (non-dummy) output record
//!     - if the mode is `conserve`, there should be two (non-dummy) input notes
//!     - if the mode is `conserve`, the value of assets in & out
//!       with same id should be conserved
//!

use crate::{
    circuit::{
        local_data::local_data_commitment_circuit,
        structs::{NoteInputVar, RecordOpeningVar},
    },
    constants::MEMO_LEN,
    errors::DPCApiError,
    predicates::PredicateTrait,
    proofs::{
        predicates::{Predicate, PredicateCircuit},
        transaction::{DPCProvingKey, DPCVerifyingKey},
    },
    structs::{NoteInput, PolicyIdentifier, RecordOpening},
    types::{InnerScalarField, InnerUniversalParam, OuterUniversalParam},
};
use ark_std::One;
use ark_std::{vec, vec::Vec, Zero};
use jf_plonk::circuit::{Arithmetization, Circuit, PlonkCircuit};

// A simple wrapper of predicate circuit
struct DexPredicateCircuit(PredicateCircuit);

impl From<PredicateCircuit> for DexPredicateCircuit {
    fn from(circuit: PredicateCircuit) -> Self {
        Self(circuit)
    }
}

// A simple wrapper of predicate
struct DexPredicate<'a>(Predicate<'a>);
impl<'a> From<Predicate<'a>> for DexPredicate<'a> {
    fn from(predicate: Predicate<'a>) -> Self {
        Self(predicate)
    }
}

enum DeathPredicateMode {
    Exchange,
    Cancel,
}

enum BirthPredicateMode {
    Mint,
    Conserve,
}

impl From<BirthPredicateMode> for usize {
    fn from(mode: BirthPredicateMode) -> Self {
        match mode {
            BirthPredicateMode::Mint => 0,
            BirthPredicateMode::Conserve => 1,
        }
    }
}

impl From<DeathPredicateMode> for usize {
    fn from(mode: DeathPredicateMode) -> Self {
        match mode {
            DeathPredicateMode::Exchange => 2,
            DeathPredicateMode::Cancel => 3,
        }
    }
}

pub struct ModeMemo([InnerScalarField; MEMO_LEN]);

impl ModeMemo {
    fn new(birth_mode: Option<BirthPredicateMode>, death_mode: Option<DeathPredicateMode>) -> Self {
        let mut memo = [InnerScalarField::zero(); MEMO_LEN];
        if let Some(mode) = birth_mode {
            let i: usize = mode.into();
            memo[i] = InnerScalarField::one();
        }
        if let Some(mode) = death_mode {
            let i: usize = mode.into();
            memo[i] = InnerScalarField::one();
        }
        Self(memo)
    }
}

// Using the default birth predicate circuit to argue
// 1. all asset_ids match
// 2. sum inputs = sum outputs
// 3. all the inputs are correctly w.r.t. commitment
impl DexPredicateCircuit
where
    Self: Sized + From<PredicateCircuit>,
{
    // Our code requires that #gates in a birth circuit to be greater
    // than that of a death circuit. If birth circuit has smaller size,
    // we need to pad the birth circuit to make it larger.
    //
    // Our death circuit performs a valid_note_gate check which will
    // not exceed 1024 constraints
    const PAD_GATES: usize = 1024;

    fn gen_birth_circuit_core(
        entire_input_notes: &[NoteInput],
        entire_output_records: &[RecordOpening],
        memo: &[InnerScalarField; MEMO_LEN],
        blinding_local_data: InnerScalarField,
        comm_local_data: InnerScalarField,
    ) -> Result<Self, DPCApiError> {
        let mut birth_circuit = PlonkCircuit::new_turbo_plonk();

        // build all the variables
        let comm_local_data_var = birth_circuit.create_public_variable(comm_local_data)?;
        let blinding_local_data_var = birth_circuit.create_variable(blinding_local_data)?;

        let entire_input_notes_vars = entire_input_notes
            .iter()
            .map(|x| NoteInputVar::new(&mut birth_circuit, x))
            .collect::<Result<Vec<_>, _>>()?;
        let entire_outputs_vars = entire_output_records
            .iter()
            .map(|x| RecordOpeningVar::new(&mut birth_circuit, x))
            .collect::<Result<Vec<_>, _>>()?;
        let memo_vars = memo
            .iter()
            .map(|x| birth_circuit.create_variable(*x))
            .collect::<Result<Vec<_>, _>>()?;

        // 1. argue that the local data is correct w.r.t. to the commitment of local
        // data
        local_data_commitment_circuit(
            &mut birth_circuit,
            &entire_input_notes_vars,
            &entire_outputs_vars,
            &memo_vars,
            &blinding_local_data_var,
            &comm_local_data_var,
        )?;

        // 2. enforce that there are only 2 input notes and 2 output records
        let num_input_notes = birth_circuit
            .create_variable(InnerScalarField::from(entire_input_notes.len() as u64))?;
        let num_output_records = birth_circuit
            .create_variable(InnerScalarField::from(entire_output_records.len() as u64))?;

        // expect two input notes and two output records, plus one fee record for each
        let num_of_fee_records = 1u64;
        let expected_notes_var = birth_circuit
            .create_constant_variable(InnerScalarField::from(2u64 + num_of_fee_records))?;
        let is_input_two = birth_circuit.check_equal(num_input_notes, expected_notes_var)?;
        let is_output_two = birth_circuit.check_equal(num_output_records, expected_notes_var)?;
        // they should both be satisfied
        let res = birth_circuit.logic_and(is_input_two, is_output_two)?;
        birth_circuit.equal_gate(res, birth_circuit.one())?;

        // 3. memo should only have one of the first two bits set to 1
        let is_mint = memo_vars[0];
        let is_conserve = memo_vars[1];
        let mint_and_converve_var = birth_circuit.logic_and(is_mint, is_conserve)?;
        // they are not both == 1
        birth_circuit.equal_gate(mint_and_converve_var, birth_circuit.zero())?;
        // but one of them is 1
        birth_circuit.logic_or_gate(is_mint, is_conserve)?;

        // 4. check mode mint & conserve
        let one_var = birth_circuit.one();
        let zero_var = birth_circuit.zero();
        // when the mode is mint, inputs should be dummy, check AND(input_1.is_dummy, input_2.is_dummy) == 1
        let mut is_mint_satisfied = birth_circuit.create_variable(InnerScalarField::one())?;
        // when mode is conserve, none of the inputs should be dummy, check OR(input_1.is_dummy, input_2.is_dummy) == 0
        let mut is_conserve_satisfied = birth_circuit.create_variable(InnerScalarField::zero())?;
        // check that all inputs are dummy for mint, and none are dummy if conserve
        for input in entire_input_notes_vars
            .iter()
            .skip(num_of_fee_records as usize)
        {
            let is_dummy_var = input.record_opening_var.payload.is_dummy;
            is_mint_satisfied = birth_circuit.logic_and(is_dummy_var, is_mint_satisfied)?;
            is_conserve_satisfied = birth_circuit.logic_or(is_dummy_var, is_conserve_satisfied)?;
        }
        // mint mode is satisfied if all inputs are dummy
        let is_mint_satisfied = birth_circuit.check_equal(is_mint_satisfied, one_var)?;
        // conserve mode is satisfied if all inputs are not dummy
        let is_conserve_satisfied = birth_circuit.check_equal(is_conserve_satisfied, zero_var)?;

        // check that the mode is satisfied as dictated by the memo
        birth_circuit.equal_gate(is_mint_satisfied, is_mint)?;
        birth_circuit.equal_gate(is_conserve_satisfied, is_conserve)?;

        // pad the birth circuit with dummy gates so that it will always be greater
        // than the supported death ones
        birth_circuit.pad_gate(Self::PAD_GATES);

        Ok(Self::from(PredicateCircuit(birth_circuit)))
    }

    fn preprocessed_birth_circuit(entire_input_size: usize) -> Result<Self, DPCApiError> {
        let proof_gen_key = crate::keys::ProofGenerationKey::default();

        let dummy_blinding_local_data = InnerScalarField::default();
        let dummy_comm_local_data = InnerScalarField::default();
        let dummy_input_notes = vec![NoteInput::dummy(&proof_gen_key); entire_input_size];
        let dummy_output_records = vec![RecordOpening::dummy(); entire_input_size];
        let dummy_memo = [InnerScalarField::zero(); MEMO_LEN];

        Self::gen_birth_circuit_core(
            &dummy_input_notes,
            &dummy_output_records,
            &dummy_memo,
            dummy_blinding_local_data,
            dummy_comm_local_data,
        )
    }

    fn gen_birth_circuit(
        entire_input_notes: &[NoteInput],
        entire_output_records: &[RecordOpening],
        memo: &[InnerScalarField; MEMO_LEN],
        blinding_local_data: InnerScalarField,
        comm_local_data: InnerScalarField,
    ) -> Result<Self, DPCApiError> {
        Self::gen_birth_circuit_core(
            entire_input_notes,
            entire_output_records,
            memo,
            blinding_local_data,
            comm_local_data,
        )
    }
}

// Extra, application dependent logics are defined in this circuit.
impl DexPredicateCircuit
where
    Self: Sized + From<PredicateCircuit>,
{
    // we want to check:
    //  - it uses a same local data commitment as the birth predicate
    //  - each input/output value is within {0, 1, 5, 10, 50, 100}
    fn gen_death_circuit_core(
        entire_input_notes: &[NoteInput],
        entire_output_records: &[RecordOpening],
        memo: &[InnerScalarField; MEMO_LEN],
        blinding_local_data: InnerScalarField,
        comm_local_data: InnerScalarField,
    ) -> Result<Self, DPCApiError> {
        let mut death_circuit = PlonkCircuit::new_turbo_plonk();

        // build all the variables
        let comm_local_data_var = death_circuit.create_public_variable(comm_local_data)?;
        let blinding_local_data_var = death_circuit.create_variable(blinding_local_data)?;

        let entire_input_notes_vars = entire_input_notes
            .iter()
            .map(|x| NoteInputVar::new(&mut death_circuit, x))
            .collect::<Result<Vec<_>, _>>()?;
        let entire_outputs_vars = entire_output_records
            .iter()
            .map(|x| RecordOpeningVar::new(&mut death_circuit, x))
            .collect::<Result<Vec<_>, _>>()?;
        let memo_vars = memo
            .iter()
            .map(|x| death_circuit.create_variable(*x))
            .collect::<Result<Vec<_>, _>>()?;

        // argue that the local data is correct w.r.t. to the commitment of local data
        local_data_commitment_circuit(
            &mut death_circuit,
            &entire_input_notes_vars,
            &entire_outputs_vars,
            &memo_vars,
            &blinding_local_data_var,
            &comm_local_data_var,
        )?;

        // pad the death circuit with dummy gates
        let current_gate_count = death_circuit.num_gates();
        let target_gate_count = Self::preprocessed_birth_circuit(entire_input_notes.len())?
            .0
             .0
            .num_gates();
        death_circuit.pad_gate(target_gate_count - current_gate_count);

        Ok(DexPredicateCircuit(PredicateCircuit(death_circuit)))
    }

    fn preprocessed_death_circuit(entire_input_size: usize) -> Result<Self, DPCApiError> {
        let proof_gen_key = crate::keys::ProofGenerationKey::default();

        let dummy_blinding_local_data = InnerScalarField::default();
        let dummy_comm_local_data = InnerScalarField::default();
        let dummy_input_notes = vec![NoteInput::dummy(&proof_gen_key); entire_input_size];
        let dummy_output_records = vec![RecordOpening::dummy(); entire_input_size];
        let dummy_memo = [InnerScalarField::zero(); MEMO_LEN];

        Self::gen_death_circuit_core(
            &dummy_input_notes,
            &dummy_output_records,
            &dummy_memo,
            dummy_blinding_local_data,
            dummy_comm_local_data,
        )
    }

    fn gen_death_circuit(
        entire_input_notes: &[NoteInput],
        entire_output_records: &[RecordOpening],
        memo: &[InnerScalarField; MEMO_LEN],
        blinding_local_data: InnerScalarField,
        comm_local_data: InnerScalarField,
    ) -> Result<Self, DPCApiError> {
        Self::gen_death_circuit_core(
            entire_input_notes,
            entire_output_records,
            memo,
            blinding_local_data,
            comm_local_data,
        )
    }
}

impl<'a> DexPredicate<'a>
where
    Self: Sized + From<Predicate<'a>>,
{
    /// Setup the circuit and related parameters
    ///
    /// Inputs:
    /// - rng
    /// - inner SRS
    /// - outer SRS
    /// - total number of inputs (including fee record)
    ///
    /// Outputs:
    /// - DPC proving key
    /// - DPC verification key
    /// - Birth predicate (with dummy local commitment)
    /// - Birth predicate PIDs
    /// - Death predicate (with dummy local commitment)
    /// - Death predicate PIDs
    fn preprocess(
        inner_srs: &'a InnerUniversalParam,
        outer_srs: &'a OuterUniversalParam,
        entire_input_size: usize,
    ) -> Result<
        (
            DPCProvingKey<'a>,
            DPCVerifyingKey,
            Self,
            PolicyIdentifier,
            Self,
            PolicyIdentifier,
        ),
        DPCApiError,
    > {
        // setup the dummy circuit/predicate/pid
        let mut birth_predicate_circuit =
            DexPredicateCircuit::preprocessed_birth_circuit(entire_input_size)?;
        let death_predicate_circuit =
            DexPredicateCircuit::preprocessed_death_circuit(entire_input_size)?;
        let birth_predicate = Predicate::new(inner_srs, &birth_predicate_circuit.0, true)?;
        let death_predicate = Predicate::new(inner_srs, &death_predicate_circuit.0, false)?;
        let birth_pid = PolicyIdentifier::from_verifying_key(birth_predicate.verifying_key());
        let death_pid = PolicyIdentifier::from_verifying_key(death_predicate.verifying_key());

        birth_predicate_circuit
            .0
             .0
            .finalize_for_mergeable_circuit(jf_plonk::MergeableCircuitType::TypeA)?;

        // the inner domain size is the birth (or death) circuit's domain size
        let inner_domain_size = birth_predicate_circuit.0 .0.eval_domain_size()?;

        let (dpc_pk, dpc_vk, (..)) = crate::proofs::transaction::preprocess(
            outer_srs,
            inner_srs,
            entire_input_size - 1,
            inner_domain_size,
        )?;
        Ok((
            dpc_pk,
            dpc_vk,
            Self::from(birth_predicate),
            birth_pid,
            Self::from(death_predicate),
            death_pid,
        ))
    }

    /// Finalize a predicate circuit.
    ///
    /// This function will need to be called to prepare
    /// the circuit for proof generation.
    /// When a predicate circuit was initialized, it does not have the
    /// correct commitment to the local data (and thus cannot generate)
    /// a correct proof.
    fn finalize_for_proving(
        &mut self,
        entire_input_notes: &[NoteInput],
        entire_output_records: &[RecordOpening],
        memo: &[InnerScalarField; MEMO_LEN],
        blinding_local_data: InnerScalarField,
        comm_local_data: InnerScalarField,
        is_birth_predicate: bool,
    ) -> Result<(), DPCApiError> {
        let mut final_circuit = if is_birth_predicate {
            DexPredicateCircuit::gen_birth_circuit(
                entire_input_notes,
                entire_output_records,
                memo,
                blinding_local_data,
                comm_local_data,
            )?
        } else {
            DexPredicateCircuit::gen_death_circuit(
                entire_input_notes,
                entire_output_records,
                memo,
                blinding_local_data,
                comm_local_data,
            )?
        };

        // sanity check: circuit is satisfied
        final_circuit
            .0
             .0
            .check_circuit_satisfiability(&[comm_local_data])?;

        // finalize the circuit, and update the witness accordingly

        let circuit_type = if is_birth_predicate {
            jf_plonk::MergeableCircuitType::TypeA
        } else {
            jf_plonk::MergeableCircuitType::TypeB
        };

        final_circuit
            .0
             .0
            .finalize_for_mergeable_circuit(circuit_type)?;

        self.0.update_witness(final_circuit.0)?;
        Ok(())
    }
}

#[cfg(test)]
mod dex_tests;
