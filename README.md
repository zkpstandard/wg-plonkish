**Plonkish Constraint System**

**Team:** 
Jack Grigg, Electric Coin Company, jack@electriccoin.co
Daira Emma Hopwood, Electric Coin Company, daira@electriccoin.co
Mary Maller, Ethereum Foundation and PQShield, mary.maller@ethereum.org

*Public Contact:*  jack@electriccoin.co, daira@electriccoin.co, mary.maller@ethereum.org

**Expected deliverables**
The working group will focus on the Plonkish arithmetisation used in the Halo2 proving system.  The initial deliverable will be split into two draft specifications:  the Plonkish constraint system specification and the optimised Plonkish constraint specification.  The constraint system will be agnostic to the underlying prime ordered field.  The output is expected to be used as input to e.g., an interactive oracle proof. 

The Plonkish constraint system specification will detail
* The fixed, public, and private inputs to the Plonkish relation
* The supported constraints in the Plonkish predicate.
* The format of any additional auxiliary hints that are useful for later optimisation steps.

The supported constraints will include custom constraints, copy constraints, and both static and dynamic lookup constraints.

The optimised Plonkish constraint system will detail
* The fixed, public, and private inputs to the optimised Plonkish relation
* The notion of abstract columns that do not correspond 1:1 to the actual columns in the concrete circuit.
* The notion of used constraints, which indicate which advice coordinates are nontrivially used.
* Additional support for rotation constraints
* How to compile to the optimised circuit

The optimised Plonkish constraint system will aim to minimise the number of copy constraints.  It will include a backend that rearranges the order of the constraints in order satisfy rotation constraints that reduce the number of copy constraints.

Accompanying the specification will be an open-source reference implementation written in rust and accompanying test vectors.  We also intend to include a hax implementation to formally check that the optimisations included in the optimised constraint system preserve the knowledge soundness and the zero-knowledge of the unoptimised constraint system.

**Time Frame**
The team will meet once every two weeks during 2024 and aims to have an initial draft specification by June 2024.

*References:* 
[The Halo2 Book](https://zcash.github.io/halo2/concepts/arithmetization.html)
[UltraPlonk Arithmetisation](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-turbo_plonk.pdf)
[Plaf format](https://github.com/Dhole/polyexen/blob/master/plaf.md)
[hax](https://github.com/hacspec/hax)

*Submitted on YYYY-Month-DD to the ZKProof Standards Committee.*