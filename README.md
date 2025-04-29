# Plonkish Constraint Systems

As part of the [ZKProof standardization effort](https://zkproof.org), the
Plonkish Constraint System Working Group is developing a specification, a
reference implementation written in Rust, and test vectors for
*Plonkish arithmetisation*.

See also [Mary's presentation about the Plonkish Working Group](https://zkproof.org/2023/09/12/plonk-standardization-zkproof-5-5-mary-maller-talk-summary/).

Plonkish arithmetisation is a means of expressing circuits for probabilistic
and/or zero-knowledge proving systems. This arithmetisation was originally
developed in the context of the [PLONK](https://eprint.iacr.org/2019/953)
proving system, and refined for use in the [Halo 2](https://zcash.github.io/halo2/)
proving system. The variant of Plonkish used by Halo 2 is the initial focus
for this standardization effort.

## Security Warnings

The software and specifications in this repository are currently under
development and have not been fully reviewed.

## Rust prerequisites

- `cargo install mdbook`
- `cargo install mdbook-katex`

## Rendering

- `mdbook build`

The rendered documents can be viewed at [docs/index.html](docs/index.html).

## License

All files in this repository are licensed under any of:

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
 * Creative Commons Attribution 4.0 International ([LICENSE-CC-BY-4.0](LICENSE-CC-BY-4.0) or https://creativecommons.org/licenses/by/4.0/legalcode.en)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be triple-licensed as above, without any additional terms or
conditions.
