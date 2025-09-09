
---
stand_alone: true
ipr: trust200902
submissiontype: IETF

cat: info
title: Specification of the Plonkish Relation
author:
- name: Mary Maller
  org: Ethereum Foundation and PQShield (liaison)
- name: Daira-Emma Hopwood
  org: Jacaranda Software
- name: Jack Grigg
  org: Electric Coin Company
- name: Constance Beguier
  org: Qedit

informative:
  Thomas22:
    title: "Arithmetization of Σ¹₁ relations in Halo 2"
    author:
      - ins: M. Thomas
        name: Morgan Thomas
    date: 2022
    seriesinfo:
      IACR: ePrint Archive 2022/777
    target: https://eprint.iacr.org/2022/777
    format:
      HTML: https://eprint.iacr.org/2022/777

  ZKProofCommunityReference:
    title: "ZKProof Community Reference"
    author:
      - org: ZKProof Community
    date: 2023
    target: https://docs.zkproof.org/reference
    format:
      HTML: https://docs.zkproof.org/reference

  MultivariatePolynomial:
    title: "Polynomial ring – Definition (multivariate case)"
    author:
      - org: Wikipedia editors
    date: 2025
    target: https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)
    format:
      HTML: https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)

--- abstract

An arithmetization is a language that a proof system uses to express statements. A circuit is a program in this language. The associated computation has been computed correctly if and only if all of the constraints in the circuit are satisfied.

The primary purpose of this document is to specify a particular arithmetization: the "Plonkish" arithmetization used in the Halo 2 proving system.

--- middle

# Introduction

This document describes the general Plonkish relation used in zero-knowledge proof systems. It is based on ideas in {{Thomas22}} and is intended to be read alongside implementation-focused material.

# Dependencies and Notation

Plonkish arithmetization depends on a field over a prime modulus `p`. Integers taken modulo the field modulus `p` are called field elements and their type is denoted as `Fp`; arithmetic operations on field elements are implicitly performed modulo `p`. We denote the additive identity by `0` and the multiplicative identity by `1`.  We denote the sum, difference, and product of two field elements using the `+`, `-`, and `·` operators, respectively.

`Nat` refers to the type of natural numbers, and `Int` to the type of integers.

The notation `a..b` means the sequence of integers from `a` (inclusive) to `b` (exclusive) in ascending order.

The notation `x : T` means that `x` is of type `T`.

`T × U` means the type of pairs with first element from the type `T`, and second element from the type `U`.

`T -> U` means the type of functions with range type `T` and domain type `U`.

`[n]` means the type of natural numbers from `0` (inclusive) to `n` (exclusive).

`T^[m]` means the type of sequences indexed by `[m]` with elements from type `T`.

`T^[m × n]` means the type of matrices indexed first by a column index in `[m]` and then by a row index in `[n]`, with elements from type `T`. That is, if `w : T^[m × n]` then `w[i, j]` means the element at column index `i : [m]` and row index `j : [n]`.

If `X` is a field element, on the other hand, then `X^e` means the result of raising `X` to the integer power `e`. There are no square brackets around the exponent in this case.

The length of a sequence `S`, or the number of elements in a set `S`, is written `#S`.

The condition that `e` is a member of the set `S` is written `e ∈ S`.

`Set⟨T⟩` means the type of sets with elements in `T`. `Equiv⟨T⟩` means the type of equivalence relations (i.e. reflexive, symmetric, and transitive binary relations) on `T`.

`[ f(e) | e <- a..b ]` means the sequence of evaluations of `f` on `a..b`.

`[ f(e) | e ]` means the sequence of evaluations of `f` for some implicitly defined sequence of zero-based indices `e`.

`Σ S` means the sum of a sequence `S` of field elements, and `Π S` means the product.

`=>` means logical implication.

When `f` is a function that takes a tuple as argument, we will allow `f((i, j))` to be written as `f[i, j]`.

The terminology used here is intended to be consistent with the ZKProof Community Reference {{ZKProofCommunityReference}}. We diverge from this terminology as follows:
* We refer to the public inputs to the circuit as an "instance vector". The entries of this vector are called "instance variables" in the Community Reference.

# The General Plonkish Relation `R_plonkish`

The general relation `R_plonkish` contains pairs of `(x, w)` where:
* the instance `x` consists of the parameters of the proof system, the circuit `C`, and the public inputs to the circuit (i.e. the instance vector).
* the witness `w` consists of the matrix of values provided by the prover. In this model it consists of the (potentially private) prover inputs to the circuit, and any intermediate values (including fixed values) that are not inputs to the circuit but are required in order to satisfy it.

We say that a `x` is a *valid* instance whenever there exists some witness `w` such that `(x, w) ∈ R_plonkish` holds.
The Plonkish language `L_plonkish` contains all valid instances.

A circuit-specific relation is a specialization of `R_plonkish` to a particular circuit.

If the proof system is knowledge sound, then the prover must have knowledge of the witness in order to construct a valid proof. If it is also zero knowledge, then witness entries can be private, and an honestly generated proof leaks no information about the private inputs to the circuit beyond the fact that it was obtained with knowledge of some satisfying witness.

## Instances

The relation `R_plonkish` takes instances of the following form:

| Instance element             | Description                                                                  |
| ---------------------------- | ---------------------------------------------------------------------------- |
| `     Fp                   ` | A prime field.                                                               |
| `      C                   ` | The circuit.                                                                 |
| `      ϕ : Fp^[C.t]        ` | The instance vector, where `t` is the instance vector length defined below). |

The circuit `C : AbstractCircuit_Fp` in turn has the following form:

| Circuit element              | Description                                                                                    | Used in                                   |
| ---------------------------- | ---------------------------------------------------------------------------------------------- | ----------------------------------------- |
| `      t : Nat             ` | Length of the instance vector.                                                                 |                                           |
| `      n : Nat | n > 0     ` | Number of rows for the witness matrix.                                                         |                                           |
| `      m : Nat | m > 0     ` | Number of columns for the witness matrix.                                                      |                                           |
| `      ≡ : Equiv⟨[m] × [n]⟩` | An equivalence relation indicating which witness entries are equal to each other.              | [Copy constraints](#copy-constraints)     |
| `      S : ([m] × [n])^t`    | A vector indicating witness entries to be constrained to match the instance vector.            | [Copy constraints](#copy-constraints)     |
| `    m_f : Nat | m_f ≤ m   ` | Number of columns that are fixed.                                                              | [Fixed constraints](#fixed-constraints)   |
| `      f : Fp^[m_f × n]    ` | The fixed content of the first `m_f` columns.                                                  | [Fixed constraints](#fixed-constraints)   |
| `    p_u : Fp^[m] -> Fp    ` | Custom multivariate polynomials.                                                               | [Custom constraints](#custom-constraints) |
| `  CUS_u : Set⟨[n]⟩        ` | Sets indicating rows on which the custom polynomials `p_u` are constrained to evaluate to `0`. | [Custom constraints](#custom-constraints) |
| `    L_v : Nat             ` | Number of table columns in the lookup table with index `v`.                                    | [Lookup constraints](#lookup-constraints) |
| `  TAB_v : Set⟨Fp^[L_v]⟩   ` | Lookup tables `TAB_v` each containing a set of sequences of type `Fp^[L_v]`.                   | [Lookup constraints](#lookup-constraints) |
| `q_{v,s} : Fp^[m] -> Fp    ` | Scaling multivariate polynomials `q_{v,s}` for `s : [L_v]`.                                    | [Lookup constraints](#lookup-constraints) |
| ` LOOK_v : Set⟨[n]⟩        ` | Sets indicating rows on which scaling polynomials `q_{v,s}` evaluate to some tuple in `TAB_v`. | [Lookup constraints](#lookup-constraints) |

## Witnesses

The relation `R_plonkish` takes witnesses of the following form:

| Witness element              | Description         |
| ---------------------------- | ------------------- |
| `      w : Fp^[m × n]      ` | The witness matrix. |

Define `vec_w_j` as the row vector `[ w[i, j] | i <- 0..m ]`.

## Definition of the relation

Given the above definitions, the relation `R_plonkish` corresponds to a set of (instance, witness) pairs:

- `x`:
  - `Fp`
  - `C`:
    - `t`, `n`, `m`, `≡`, `S`, `m_f`, `f`
    - `[ (p_u, CUS_u) | u ]`
    - `[ (L_v, TAB_v, [q_{v,s} | s], LOOK_v) | v ]`
  - `ϕ`
- `w`

such that:

| Domains                                                                | Constraints                                                |
| -----------------------------------------------------------------------| ---------------------------------------------------------- |
| `w : Fp^[m × n]`, `f : Fp^[m_f × n]`                                   | `i : [m_f], j : [n] => w[i, j] = f[i, j]`                  |
| `S : ([m] × [n])^[t]`, `ϕ : Fp^[t]`                                    | `k : [t] => w[S[k]] = ϕ[k]`                                |
| `≡ : Equiv([m] × [n])`                                                 | `(i, j) ≡ (k, l) => w[i, j] = w[k, l]`                     |
| `CUS_u : Set⟨[n]⟩`, `p_u : Fp^[m] -> Fp`                               | `j ∈ CUS_u => p_u(vec_w_j) = 0`                            |
| `LOOK_v : Set⟨[n]⟩`, `q_{v,s} : Fp^[m] -> Fp`, `TAB_v : Set⟨Fp^[L_v]⟩` | `j ∈ LOOK_v => [ q_{v,s}(vec_w_j) | s <- 0..L_v ] ∈ TAB_v` |

In this model, a circuit-specific relation `R_{Fp, C}` for a field `Fp` and circuit `C` is the relation `R_plonkish` restricted to the subset of instances and witnesses `( (Fp, C, ϕ : Fp^[C.t]), w : Fp^[C.m × C.n])`

## Conditions satisfied by statements in `R_plonkish`

There are four types of constraints that a Plonkish statement `(x, w) ∈ R_plonkish` must satisfy:

* Fixed constraints
* Copy constraints
* Custom constraints
* Lookup constraints

### Fixed constraints

The first `m_f` columns of `w` are fixed to the columns of `f`.

### Copy constraints

Copy constraints enforce that entries in the witness matrix are equal to each other, or that an instance entry is equal to a witness entry.

| Copy Constraints                     | Description                                                                                  |
| ------------------------------------ | -------------------------------------------------------------------------------------------- |
| `k : [t] => w[S[k]] = ϕ[k]`.         | The instance entry at index `k` is equal to the advice entry at location `(i,j) = S[k]`.     |
| `(i,j) ≡ (k,l) => w[i, j] = w[k, l]` | `≡` is an equivalence relation indicating which witness entries are constrained to be equal. |

By convention, when fixed abstract cells have the same value, we consider them to be equivalent under `≡`. That is, if `i < m_f` and `k < m_f` and `f[i, j] = f[k, l]` then `(i, j) ≡ (k, l)`.

This has no direct effect on the relation, but it will simplify expressing an optimization.

### Custom constraints

Plonkish also allows custom constraints between the witness matrix entries. In the abstract model we are defining, a custom constraint applies only within a single row of the witness matrix, for the rows that are selected for that constraint.

In some systems using Plonkish, custom constraints are referred to as "gates".

Custom constraints enforce that witness entries within a row satisfy some multivariate polynomial. Here `p_u` could indicate any case that can be generated using a combination of multiplications and additions.

| Custom Constraints                   | Description                                                                                                                      |
| ------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------- |
| `j ∈ CUS_u => p_u(vec_w_j) = 0`      | `u` is the index of a custom constraint. `j` ranges over the set of rows `CUS_u` for which the custom constraint is switched on. |

Here `p_u : Fp^[m] -> Fp` is an arbitrary [multivariate polynomial](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)):

> Given `η` symbols `X_b` for `b : [η]` called indeterminates, a multivariate polynomial `P` in these indeterminates with coefficients in `Fp` is a finite linear combination
>
> `P([ X_b | b <- 0..η ]) = Σ [ c_z · Π [ X_b^{α_{z,b}} | b <- 0..η ] | z <- 0..ν ]`
>
> where  `c_z : Fp | c_z ≠ 0`, `ν : Nat`, and `α_{z,b} : Nat`.

### Lookup constraints

Lookup constraints enforce that some polynomial function of the witness entries on a row are contained in some table.

The sizes of tables are not limited at this layer. A realization of a proving system using Plonkish arithmetization may limit the supported size of tables, possibly depending on `n`, or it may have some way to compile larger tables.

In this specification, we only support fixed lookup tables determined in advance. This could be generalized to support dynamic tables determined by part of the witness matrix.

| Lookup Constraints                                         | Description                                                                                                                  |
| ---------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| `j ∈ LOOK_v => [ q_{v,s}(vec_w_j) | s <- 0..L_v ] ∈ TAB_v` | `v` is the index of a lookup table. `j` ranges over the set of rows `LOOK_v` for which the lookup constraint is switched on. |

Here `q_{v,s} : Fp^[m] -> Fp` for `s : [L_v]` are multivariate polynomials that collectively map the witness entries `vec_w_j` on the lookup row `j ∈ LOOK_v` to a tuple of field elements. This tuple will be constrained to match some row of the table `TAB_v`.

# IANA Considerations

This document has no actions for IANA.

--- back

# Acknowledgements

Morgan Thomas
Oana Ciobotaru
Kris Nuttycombe
Sean Bowe
Jonathan Rouach
The organizers and participants of the ZKProof workshops.
