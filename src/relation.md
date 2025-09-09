# Specification of the Plonkish Relation

## Objectives
- Need to agree on the API between “zkInterface for Plonkish” and the proving system.  Specify a general statement that the proving system has to implement.
- Section 2 of [[Thomas 2022]](https://eprint.iacr.org/2022/777.pdf) : describes high level API of zk Interface for Plonkish statements

This is intended to be read in conjunction with the [Plonkish Backend Optimizations](optimizations.md) document, which describes how to compile the abstract constraint system described here into a concrete circuit.

## Dependencies and notation

Plonkish arithmetization depends on a scalar field over a prime modulus $p$. We represent this field as the object $\F$. We denote the additive identity by $0$ and the multiplicative identity by $1$. Integers, taken modulo the field modulus $p$, are called scalars; arithmetic operations on scalars are implicitly performed modulo $p$. We denote the sum, difference, and product of two scalars using the $+$, $-$, and $*$ operators, respectively.

The notation $\range{a}{b}$ means the sequence of integers from $a$ (inclusive) to $b$ (exclusive) in ascending order. $[a, b)$ means the corresponding set of integers.

The length of a sequence $S$, or the number of elements in a set $S$, is written $\#S$.

$\setof{f(e) \where e \in S}$ means the set of evaluations of $f$ on the set $S$.

$\vecof{f(e) \where e \gets \range{a}{b}}$ means the sequence of evaluations of $f$ on $\range{a}{b}$.

$\vecof{A_e}_e$ means the sequence of $A_e$ for some implicitly defined sequence of indices $e$.

When $f$ is a function that takes a tuple as argument, we will allow $f((i, j))$ to be written as $f[i, j]$.

The terminology used here is intended to be consistent with the [ZKProof Community Reference](https://docs.zkproof.org/reference). We diverge from this terminology as follows:
* We refer to the public inputs to the circuit as an "instance vector". The entries of this vector are called "instance variables" in the Community Reference.

## The General Plonkish Relation $\cR_\plonkish$

The general relation $\cR_\plonkish$ contains pairs of $(x, w)$ where:
* the instance $x$ consists of the parameters of the proof system, the circuit $C$, and the public inputs to the circuit (i.e. the instance vector).
* the witness $w$ consists of the matrix of values provided by the prover. In this model it consists of the (potentially private) prover inputs to the circuit, and any intermediate values (including fixed values) that are not inputs to the circuit but are required in order to satisfy it.

We say that a $x$ is a *valid* instance whenever there exists some witness $w \suchthat (x, w) \in \cR_\plonkish$ holds.
The Plonkish language $\cL_\plonkish$ contains all valid instances.

A circuit-specific relation is a specialization of $\cR_\plonkish$ to a particular circuit.

If the proof system is knowledge sound, then the prover must have knowledge of the witness in order to construct a valid proof. If it is also zero knowledge, then witness entries can be private, and an honestly generated proof leaks no information about the private inputs to the circuit beyond the fact that it was obtained with knowledge of some satisfying witness.

### Instances

The relation $\cR_\plonkish$ takes instances of the following form:

| Instance element  | Description |
| ----------------- | ----------- |
| $\F$              | A prime field. |
| $C$               | The circuit. |
| $\phi$            | The instance vector $\phi \typecolon \F^{C.t}$ (where $t$ is the instance vector length defined below). |

The circuit $C \typecolon \mathsf{AbstractCircuit}_{\F}$ in turn has the following form:

| Circuit element   | Description | Used in |
| ----------------- | ----------- | ------- |
| $t$               | Length of the instance vector. |  |
| $n > 0$           | Number of rows for the witness matrix. |  |
| $m > 0$           | Number of columns for the witness matrix. |  |
| $\equiv$          | An equivalence relation on $[0,m) \times [0,n)$ indicating which witness entries are equal to each other. | [Copy constraints](#copy-constraints) |
| $S$               | A vector $S \typecolon ([0,m) \times [0,n))^t$ indicating witness entries to be constrained to match the instance vector. | [Copy constraints](#copy-constraints) |
| $m_f \leq m$      | Number of columns that are fixed. | [Fixed constraints](#fixed-constraints) |
| $f$               | The fixed content of the first $m_f$ columns, $f \typecolon \F^{m_f \times n}$. | [Fixed constraints](#fixed-constraints) |
| $p_u$             | Custom multivariate polynomials $p_u \typecolon \F^m \to \F$. | [Custom constraints](#custom-constraints) |
| $\CUS_u$          | Sets $\CUS_u \subseteq [0,n)$ indicating rows on which the custom polynomials $p_u$ are constrained to evaluate to 0. | [Custom constraints](#custom-constraints) |
| $L_v$             | Number of table columns in the lookup table with index $v$, $\TAB_v$. | [Lookup constraints](#lookup-constraints) |
| $\TAB_v$          | Lookup tables $\TAB_v \subseteq \F^{L_v}$, each with a number of tuples in $\F^{L_v}$. | [Lookup constraints](#lookup-constraints) |
| $q_{v,s}$         | Scaling multivariate polynomials $q_{v,s} \typecolon \F^m \to \F$ for $s \gets \range{0}{L_v}$. | [Lookup constraints](#lookup-constraints) |
| $\LOOK_v$         | Sets $\LOOK_v \subseteq [0,n)$ indicating rows on which the scaling polynomials $q_{v,s}$ evaluate to some tuple in $\TAB_v$. | [Lookup constraints](#lookup-constraints) |

Multivariate polynomials are defined below in the [Custom constraints](#custom-constraints) section.

### Witnesses

The relation $\cR_\plonkish$ takes witnesses of the following form:

| Witness element   | Description |
| ----------------- | -------- |
| $w$               | The witness matrix $w \typecolon \F^{m \times n}$. |

Define $\vec{w}_j$ as the row vector $\vecof{w[i, j] \where i \gets \range{0}{m}}$.

### Definition of the relation

Given the above definitions, the relation $\cR_\plonkish$ corresponds to a set of $\,(\!$ instance $\!,\,$ witness $\!)\,$ pairs
$$
\left(x = \left(\F, C = \left(t, n, m, \equiv, S, m_f, f, \left[\, (p_u, \CUS_{u}) \,\right]_u, \left[\, (L_v, \TAB_v, \left[\, q_{v,s} \,\right]_s, \LOOK_v) \,\right]_v\right), \phi\right),\, w \right)
$$
such that:
$$
\begin{array}{ll|l}
   w \typecolon \F^{m \times n}, \ f \typecolon \F^{m_f \times n} & & i \in [0,m_f), \ j \in [0,n) \implies w[i, j] = f[i, j] \\[0.3ex]
   S \typecolon ([0,m) \times [0,n))^t, \ \phi \typecolon \F^t & & k \in [0,t) \implies w[S[k]] = \phi[k] \\[0.3ex]
   \equiv\; \subseteq ([0,m) \times [0,n)) \times ([0,m) \times [0,n)) & & (i,j) \equiv (k,\ell) \implies w[i, j] = w[k, \ell] \\[0.3ex]
   \CUS_u \subseteq [0,n), \ p_u \typecolon \F^m \to \F & & j \in \CUS_u \implies p_u(\vec{w}_j) = 0 \\[0.3ex]
   \LOOK_v \subseteq [0,n), \ q_{v,s} \typecolon \F^m \to \F, \ \TAB_v \subseteq \F^{L_v} & & j \in \LOOK_v \implies \vecof{q_{v,s}(\vec{w}_j) \where s \gets \range{0}{L_v}} \in \TAB_v
\end{array}
$$

In this model, a circuit-specific relation $\cR_{\F, C}$ for a field $\F$ and circuit $C$ is the relation $\cR_\plonkish$ restricted to $\{ ((\F, C, \phi \typecolon \F^{C.t}), w \typecolon \F^{C.m \times C.n}) \}$.

### Conditions satisfied by statements in $\cR_\plonkish$

There are four types of constraints that a Plonkish statement $(x, w) \in \cR_\plonkish$ must satisfy:

* Fixed constraints
* Copy constraints
* Custom constraints
* Lookup constraints

#### Fixed constraints

The first $m_f$ columns of $w$ are fixed to the columns of $f$.

#### Copy constraints

Copy constraints enforce that entries in the witness matrix are equal to each other, or that an instance entry is equal to a witness entry.

| Copy Constraints  | Description |
| ----------------- | -------- |
| $k \in [0,t) \implies w[S[k]] = \phi[k]$ | The $(i,j)$ advice entry is equal to the $k$ instance entry for $S[k] = (i,j)$. |
| $(i,j) \equiv (k,\ell) \implies w[i, j] = w[k, \ell]$ | $\equiv$ is an equivalence relation indicating which witness entries are constrained to be equal. |

By convention, when fixed abstract cells have the same value, we consider them to be equivalent under $\equiv$. That is,
$$
i < m_f \and k < m_f \and f[i, j] = f[k, \ell] \implies (i, j) \equiv (k, \ell)
$$
This has no direct effect on the relation, but it will simplify expressing an [optimization](optimizations.md).

#### Custom constraints

Plonkish also allows custom constraints between the witness matrix entries. In the abstract model we are defining, a custom constraint applies only within a single row of the witness matrix, for the rows that are selected for that constraint.

In some systems using Plonkish, custom constraints are referred to as "gates".

Custom constraints enforce that witness entries within a row satisfy some multivariate polynomial. Here $p_u$ could indicate any case that can be generated using a combination of multiplications and additions.

| Custom Constraints | Description |
| -------- | -------- | 
| $j \in \CUS_u \implies p_u(\vec{w}_j) = 0$ | $u$ is the index of a custom constraint. $j$ ranges over the set of rows $\CUS_u$ <br> for which the custom constraint is switched on. |

Here $p_u \typecolon \F^m \to \F$ is an arbitrary [multivariate polynomial](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)):

> Given $\eta$ symbols $X_0, \dots, X_{\eta-1}$ called indeterminates, a multivariate polynomial $P$ in these indeterminates, with coefficients in $\F$,
> is a finite linear combination $$P(X_0, \dots, X_{\eta-1}) = \sum_{z=0}^{\nu-1} \Big(c_z\, {\small\prod_{b=0}^{\eta-1}}\, X_b^{\alpha_{z,b}}\Big)$$ where $\nu \typecolon \N$, $c_z \typecolon \F \neq 0$, and $\alpha_{z,b} \typecolon \N$.

#### Lookup constraints

Lookup constraints enforce that some polynomial function of the witness entries on a row are contained in some table.

The sizes of tables are not limited at this layer. A realization of a proving system using Plonkish arithmetization may limit the supported size of tables, possibly depending on $n$, or it may have some way to compile larger tables.

In this specification, we only support fixed lookup tables determined in advance. This could be generalized to support dynamic tables determined by part of the witness matrix.

| Lookup Constraints | Description |
| -------- | -------- |
| $j \in \LOOK_v \implies \vecof{q_{v,s}(\vec{w}_j) \where s \gets 0}{L_v} \in \TAB_v$ | $v$ is the index of a lookup table. $j$ ranges over the set of rows $\LOOK_v$ <br> for which the lookup constraint is switched on. |

Here $q_{v,s} \typecolon \F^m \to \F$ for $s \gets \range{0}{L_v}$ are multivariate polynomials that collectively map the witness entries $\vec{w}_j$ on the lookup row $j \in \LOOK_v$ to a tuple of field elements. This tuple will be constrained to match some row of the table $\TAB_v$.
