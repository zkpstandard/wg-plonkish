# Abstract — Plonkish Constraint System Working Group

## Contributors
- Jack Grigg, Electric Coin Company
- Daira-Emma Hopwood, Jacaranda Software
- Mary Maller, Ethereum Foundation and PQShield

*Public Contact:* plonkish-team@googlegroups.com

*Submitted on 2024-MM-DD to the ZKProof Standards Committee.*

## Summary
An arithmetisation is a language that a proof system uses to express statements. A circuit is a program in this language. The associated computation has been computed correctly if and only if all of the constraints in the circuit are satisified.

The primary purpose of this ZKProof Working Group is to specify a particular arithmetisation: the "Plonkish" arithmetisation used in the Halo 2 proving system.

## Expected deliverables
The initial deliverable will be split into two draft specifications:
- The Plonkish constraint system specification.
- The optimised Plonkish constraint specification.

The constraint system specifications will be agnostic to the underlying prime-order field.  The output is expected to be used as input to e.g., an Interactive Oracle Proof.

The Plonkish constraint system specification will detail:
- The fixed, public, and private inputs (which are field elements) to the Plonkish relation.
- The supported constraints in the Plonkish predicate.
- The format of any additional auxiliary hints that are useful for later optimisation steps.

The supported constraints will include at least:
- Equality constraints (also known as copy constraints) that constrain different inputs to be equal.
- Lookup constraints, where inputs can be constrained to exist in some table. The table could be either static (with potential precomputations) or dynamic (provided within the inputs).
- Custom constraints, which are arbitrary low-degree polynomials defined over different inputs by the circuit designer.

The optimised Plonkish constraint system specification will detail:
- The notion of a *layout*, an assignment of fixed, public, and private inputs within a matrix of field elements.
- The notion of *used* matrix elements, that indicate which positions within the matrix are nontrivially used.
- The fixed, public, and private inputs to the optimised Plonkish relation.
- Support for rotation constraints, which leverage the relative positions of assigned matrix elements to reduce the size of the matrix and the number of equality constraints.
- How to compile to the optimised constraint system.

Accompanying the specification there will be an open-source reference implementation written in Rust, and corresponding test vectors.  We also intend to include an executable specification of the Plonkish relation, to facilitate formally verifying that the optimisations included in the optimised constraint system efficiently preserve the completeness, knowledge soundness, and zero-knowledge properties of proof systems applied to the unoptimised constraint system.

## Time Frame
The team will meet once every two weeks during 2024 and aims to have an initial draft specification by July 2024.

## Resources
- [The Halo2 Book](https://zcash.github.io/halo2/concepts/arithmetization.html)
- [UltraPlonk Arithmetisation](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-turbo_plonk.pdf)
- [Plaf format](https://github.com/Dhole/polyexen/blob/master/plaf.md)
- [hax](https://github.com/hacspec/hax)
