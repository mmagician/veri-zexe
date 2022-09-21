// Copyright (c) 2022 Espresso Systems (espressosys.com)
// This file is part of the VeriZexe library.

// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version. This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
// details. You should have received a copy of the GNU General Public License along with this program. If not, see <https://www.gnu.org/licenses/>.

//! This module implements a Tornado Cash style private transaction protocol,
//! where there only exists, say, six types of notes
//! - 0 token
//! - 1 token
//! - 5 tokens
//! - 10 tokens
//! - 50 tokens
//! - 100 tokens
//!
//!
//! In this example, we first properly define our customized Application which
//! is a combination of predicates and circuits
//! (which are simple wrappers of `Predicate` and `PredicateCircuit`).
//! This requires implementation of the following traits
//! - BirthPredicateCircuit
//! - DeathPredicateCircuit
//! - PredicateOps
//!
//! Once the application is built, we take the following steps to generate a
//! proof:
//! * Sample inner and outer circuit SRS
//!
//! * PredicateOps::preprocess(): upon receiving the SRSs and number of
//! inputs, it generates
//!     - dpc proving key
//!     - dpc verification key
//!     - birth predicate
//!     - policy id for birth predicate
//!     - death predicate
//!     - policy id for death predicate
//!
//! * build the notes and records for transaction
//!     - a valid fee note (valid = exist in merkle tree)
//!     - a list of valid input notes (valid = exist in merkle tree)
//!     - a fee change record
//!     - a list of output records
//! and build corresponding witnesses for this transaction
//!
//! * generate a dpc proof that consists of three components
//!     - an UTXO proof proves that both fee note and input notes are valid
//!       w.r.t. the given merkle root
//!     - a birth/death predicates proof that proves both predicates are
//!       satisfied w.r.t. the public/private inputs
//!     - a policies verification proof that proves the knowledge of predicates
//!       satisfaction.
//!
//! The first and third proofs are common in all DPC applications.
//! Application may vary in the second proof, which, in our case,
//! argues for the following knowledge
//!
//! - a death predicate that checks:
//!     - the values are correctly committed via the `common_local_data`
//!     - each input/output value is within {0, 1, 5, 10, 50, 100}
//!
//! - a birth predicate that checks:
//!     - the values are correctly committed via the `common_local_data`
//!     - the sum of input records' value matches the sum of output records'
//!       value
//!     - all input/output records shares a same asset id
//!     - the associated death pid is permitted (not implemented)
//!
//! Note that the birth predicate is identical for all three examples; and is
//! implemented via the default implementation.
//! So here we only need to write the logic for the death predicate.

use crate::{
    circuit::{
        self,
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
            DeathPredicateMode::Exchange => 0,
            DeathPredicateMode::Cancel => 1,
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
            memo[i + 2] = InnerScalarField::one();
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

        // // 3. when the mode is mint, inputs should be dummy, there should be only one non-dummy output
        let one_var = birth_circuit.one();
        // check that all inputs are dummy
        for input in entire_input_notes_vars
            .iter()
            .skip(num_of_fee_records as usize)
        {
            let is_dummy_var = input.record_opening_var.payload.is_dummy;
            birth_circuit.bool_gate(is_dummy_var)?;
            birth_circuit.equal_gate(is_dummy_var, one_var)?;
        }

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
mod test {
    use std::{println, time::Instant};

    use super::*;
    use crate::{
        constants::MEMO_LEN,
        errors::DPCApiError,
        examples::tests::{build_dex_notes_and_records, build_notes, DexRecord},
        keys::KeyChainMasterKey,
        proofs::transaction::*,
        structs::compress_local_data,
        types::InnerScalarField,
    };

    use ark_ec::bls12::Bls12;
    use ark_ff::{UniformRand, Zero};
    use ark_serialize::CanonicalDeserialize;
    use ark_std::{rand::Rng, test_rng, vec};
    use jf_plonk::proof_system::structs::UniversalSrs;

    const NON_NATIVE_ASSET_ID: u64 = 3u64;

    #[test]
    #[ignore]
    fn test_tornado_cash_example_transaction() -> Result<(), DPCApiError> {
        // universal setup
        // time how long it takes to do the universal setup

        let timer = Instant::now();
        // read the inner test srs from file
        let reader = std::io::BufReader::new(
            std::fs::File::open("src/examples/test_setup_inner_17.bin").unwrap(),
        );
        let inner_srs: UniversalSrs<Bls12<ark_bls12_377::Parameters>> =
            UniversalSrs::deserialize_unchecked(reader)?;
        println!("inner_srs setup time: {:?}", timer.elapsed());
        let reader = std::io::BufReader::new(
            std::fs::File::open("src/examples/test_setup_outer_18.bin").unwrap(),
        );
        let outer_srs: UniversalSrs<ark_ec::bw6::BW6<ark_bw6_761::Parameters>> =
            UniversalSrs::deserialize_unchecked(reader)?;
        println!("outer_srs setup time: {:?}", timer.elapsed());

        // good path: mode = mint, all inputs are dummy
        let fee_in = 300;
        let fee = 5;
        let fee_out = 295;
        let input_note_values = [
            DexRecord {
                asset_id: 1,
                value: 10,
                is_dummy: true,
            },
            DexRecord {
                asset_id: 1,
                value: 5,
                is_dummy: true,
            },
        ];
        let output_note_values = [
            DexRecord {
                asset_id: 1,
                value: 11,
                is_dummy: false,
            },
            DexRecord {
                asset_id: 1,
                value: 4,
                is_dummy: false,
            },
        ];
        assert!(test_example_transaction_helper(
            &inner_srs,
            &outer_srs,
            fee_in,
            fee,
            fee_out,
            input_note_values.as_ref(),
            output_note_values.as_ref(),
            Some(BirthPredicateMode::Mint),
            None
        )
        .is_ok());

        // bad path: mode = mint, one input is not dummy
        let fee_in = 300;
        let fee = 5;
        let fee_out = 295;
        let input_note_values = [
            DexRecord {
                asset_id: 1,
                value: 10,
                is_dummy: false,
            },
            DexRecord {
                asset_id: 1,
                value: 5,
                is_dummy: true,
            },
        ];
        let output_note_values = [
            DexRecord {
                asset_id: 1,
                value: 11,
                is_dummy: false,
            },
            DexRecord {
                asset_id: 1,
                value: 4,
                is_dummy: false,
            },
        ];
        assert!(test_example_transaction_helper(
            &inner_srs,
            &outer_srs,
            fee_in,
            fee,
            fee_out,
            input_note_values.as_ref(),
            output_note_values.as_ref(),
            Some(BirthPredicateMode::Mint),
            None
        )
        .is_err());

        // good path: mode = conserve
        // let fee_in = 300;
        // let fee = 5;
        // let fee_out = 295;
        // let input_note_values = [
        //     DexRecord {
        //         asset_id: 1,
        //         value: 10,
        //         is_dummy: false,
        //     },
        //     DexRecord {
        //         asset_id: 1,
        //         value: 5,
        //         is_dummy: false,
        //     },
        // ];
        // let output_note_values = [
        //     DexRecord {
        //         asset_id: 1,
        //         value: 11,
        //         is_dummy: false,
        //     },
        //     DexRecord {
        //         asset_id: 1,
        //         value: 4,
        //         is_dummy: false,
        //     },
        // ];
        // assert!(test_example_transaction_helper(
        //     &inner_srs,
        //     &outer_srs,
        //     fee_in,
        //     fee,
        //     fee_out,
        //     input_note_values.as_ref(),
        //     output_note_values.as_ref(),
        //     Some(BirthPredicateMode::Conserve),
        //     None
        // )
        // .is_ok());

        // bad path: input.len() != output.len()
        // let fee_in = 300;
        // let fee = 5;
        // let fee_out = 295;
        // let input_note_values = [
        //     DexRecord {
        //         asset_id: 1,
        //         value: 10,
        //         is_dummy: false,
        //     },
        //     DexRecord {
        //         asset_id: 1,
        //         value: 5,
        //         is_dummy: false,
        //     },
        // ];
        // let output_note_values = [
        //     DexRecord {
        //         asset_id: 1,
        //         value: 11,
        //         is_dummy: false,
        //     },
        //     DexRecord {
        //         asset_id: 1,
        //         value: 2,
        //         is_dummy: false,
        //     },
        //     DexRecord {
        //         asset_id: 1,
        //         value: 2,
        //         is_dummy: false,
        //     },
        // ];

        // assert!(test_example_transaction_helper(
        //     &inner_srs,
        //     &outer_srs,
        //     fee_in,
        //     fee,
        //     fee_out,
        //     input_note_values.as_ref(),
        //     output_note_values.as_ref(),
        //     None,
        //     Some(DeathPredicateMode::Exchange)
        // )
        // .is_err());

        Ok(())
    }

    // TODO: use the consolidated API for testing
    fn test_example_transaction_helper(
        inner_srs: &InnerUniversalParam,
        outer_srs: &OuterUniversalParam,
        fee_in: u64,
        fee: u64,
        fee_out: u64,
        input_note_values: &[DexRecord],
        output_note_values: &[DexRecord],
        birth_predicate_mode: Option<BirthPredicateMode>,
        death_predicate_mode: Option<DeathPredicateMode>,
    ) -> Result<(), DPCApiError> {
        let num_non_fee_inputs = input_note_values.len();

        let rng = &mut test_rng();

        let (dpc_pk, dpc_vk, mut birth_predicate, birth_pid, mut death_predicate, death_pid) =
            DexPredicate::preprocess(inner_srs, outer_srs, num_non_fee_inputs + 1)?;

        // generate proof generation key and addresses
        let mut wsk = [0u8; 32];
        rng.fill(&mut wsk[..]);
        let msk = KeyChainMasterKey::generate(wsk, &[]);
        let (_, pgk, ivk) = msk.derive_key_chain_single_consumer();
        let (addr, rd) = msk.derive_diversified_address(&pgk, &ivk, 0)?;

        // =================================
        // setup transaction parameters
        // we have four types of records:
        // - native token transaction fee note
        // - native token transaction fee change note
        // - Tcash input notes
        // - Tcash output notes
        // =================================
        let (entire_input_records, entire_output_records) = build_dex_notes_and_records(
            rng,
            &addr,
            &pgk,
            fee_in,
            fee_out,
            NON_NATIVE_ASSET_ID,
            input_note_values,
            output_note_values,
            birth_pid,
            death_pid,
        )?;

        let entire_input_notes = build_notes(&entire_input_records, &pgk, &rd)?;

        // prepare memo
        let dummy_memo = ModeMemo::new(birth_predicate_mode, death_predicate_mode).0;

        // update the predicates to use the correct witness circuit that matches the
        // correct local data commitment
        let compressed_local_data = compress_local_data(
            &entire_input_notes,
            &entire_output_records,
            dummy_memo.to_vec(),
        )?;

        // =================================
        // proof generation
        // =================================
        let blinding_local_data = InnerScalarField::rand(rng);
        let comm_local_data = compressed_local_data.commit(blinding_local_data)?;

        birth_predicate.finalize_for_proving(
            &entire_input_notes,
            &entire_output_records,
            &dummy_memo,
            blinding_local_data,
            comm_local_data,
            true,
        )?;
        death_predicate.finalize_for_proving(
            &entire_input_notes,
            &entire_output_records,
            &dummy_memo,
            blinding_local_data,
            comm_local_data,
            false,
        )?;

        let input_death_predicates = vec![death_predicate.0; num_non_fee_inputs];
        let output_birth_predicates = vec![birth_predicate.0; num_non_fee_inputs];

        let witness = DPCWitness::new_unchecked(
            rng,
            entire_input_notes,
            entire_output_records,
            &input_death_predicates,
            &output_birth_predicates,
            blinding_local_data,
        )?;

        let pub_input = DPCPublicInput::from_witness(
            &witness,
            fee as u64,
            dummy_memo.to_vec(),
            inner_srs.powers_of_g_ref()[1],
        )?;

        // generate the proof and verify it
        let dpc_proof = prove(rng, &dpc_pk, &witness, &pub_input)?;
        verify(&dpc_proof, &dpc_vk, &pub_input)
    }
}
