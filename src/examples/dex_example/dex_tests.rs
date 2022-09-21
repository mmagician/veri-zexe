mod test {
    use std::{println, time::Instant};

    use crate::examples::dex_example::*;
    use crate::{
        errors::DPCApiError,
        examples::tests::{build_dex_notes_and_records, build_notes, DexRecord},
        keys::KeyChainMasterKey,
        proofs::transaction::*,
        structs::compress_local_data,
        types::InnerScalarField,
    };

    use ark_ec::bls12::Bls12;
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalDeserialize;
    use ark_std::{rand::Rng, test_rng, vec};
    use jf_plonk::proof_system::structs::UniversalSrs;

    const NON_NATIVE_ASSET_ID: u64 = 3u64;

    #[test]
    #[ignore]
    fn test_dex_example_transaction() -> Result<(), DPCApiError> {
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

        // fees are the same for all tx's
        let fee_in = 300;
        let fee = 5;
        let fee_out = 295;

        let num_non_fee_inputs = 2;
        let (dpc_pk, dpc_vk, birth_predicate, birth_pid, death_predicate, death_pid) =
            DexPredicate::preprocess(&inner_srs, &outer_srs, num_non_fee_inputs + 1)?;

        // good path: mode = mint, all inputs are dummy
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
                is_dummy: true,
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
            None,
            dpc_pk.clone(),
            dpc_vk.clone(),
            birth_predicate.clone(),
            birth_pid,
            death_predicate.clone(),
            death_pid,
        )
        .is_ok(), "good path: mode = mint, all inputs are dummy");

        // bad path: mode = mint, all inputs are dummy, but two outputs are non-dummy
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
            None,
            dpc_pk.clone(),
            dpc_vk.clone(),
            birth_predicate.clone(),
            birth_pid,
            death_predicate.clone(),
            death_pid,
        )
        .is_ok(), "bad path: mode = mint, both outputs are non-dummy");

        // bad path: mode = mint, one input is not dummy
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
            None,
            dpc_pk.clone(),
            dpc_vk.clone(),
            birth_predicate.clone(),
            birth_pid,
            death_predicate.clone(),
            death_pid,
        )
        .is_err(), "bad path: mode = mint, one input is not dummy");

        // good path: mode = conserve, no dummy inputs
        let input_note_values = [
            DexRecord {
                asset_id: 1,
                value: 10,
                is_dummy: false,
            },
            DexRecord {
                asset_id: 1,
                value: 5,
                is_dummy: false,
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
            Some(BirthPredicateMode::Conserve),
            None,
            dpc_pk.clone(),
            dpc_vk.clone(),
            birth_predicate.clone(),
            birth_pid,
            death_predicate.clone(),
            death_pid,
        )
        .is_ok(), "good path: mode = conserve, no dummy inputs");

        // bad path: mode = conserve, one dummy input
        let input_note_values = [
            DexRecord {
                asset_id: 1,
                value: 10,
                is_dummy: true,
            },
            DexRecord {
                asset_id: 1,
                value: 5,
                is_dummy: false,
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
            Some(BirthPredicateMode::Conserve),
            None,
            dpc_pk.clone(),
            dpc_vk.clone(),
            birth_predicate.clone(),
            birth_pid,
            death_predicate.clone(),
            death_pid,
        )
        .is_err(), "bad path: mode = conserve, one dummy input");

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
        dpc_pk: DPCProvingKey,
        dpc_vk: DPCVerifyingKey,
        mut birth_predicate: DexPredicate,
        birth_pid: PolicyIdentifier,
        mut death_predicate: DexPredicate,
        death_pid: PolicyIdentifier,
    ) -> Result<(), DPCApiError> {
        let num_non_fee_inputs = input_note_values.len();

        let rng = &mut test_rng();

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
