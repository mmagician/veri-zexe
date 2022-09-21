#[cfg(test)]
mod test {
    
    use ark_serialize::CanonicalSerialize;
    use ark_std::{test_rng};

    use crate::proofs::{universal_setup_inner, universal_setup_outer};

    #[test]
    fn generate() {
        let rng = &mut test_rng();
        // generate an inner setup
        let max_inner_degree = (1 << 16) + 4;
        let inner_srs = universal_setup_inner(max_inner_degree, rng).unwrap();

        let writer = std::io::BufWriter::new(
            std::fs::File::create("src/examples/test_setup_inner_16.bin").unwrap(),
        );
        inner_srs.serialize_unchecked(writer);

        // generate an outer setup
        let max_outer_degree = (1 << 17) + 4;
        let outer_srs = universal_setup_outer(max_outer_degree, rng).unwrap();

        let writer = std::io::BufWriter::new(
            std::fs::File::create("src/examples/test_setup_outer_17.bin").unwrap(),
        );
        outer_srs.serialize_unchecked(writer);
    }
}
