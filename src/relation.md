# Specification of the Plonkish Relation

## Objectives
- Need to agree on the API between “zkInterface for Plonkish” and the proving system.  Specify a general statement that the proving system has to implement.
- Section 2 of [[Thomas 2022]](https://eprint.iacr.org/2022/777.pdf) : describes high level API of zk Interface for Plonkish statements.

This is intended to be read in conjunction with the [Plonkish Backend Optimizations](optimizations.md) document, which describes how to compile the abstract constraint system described here into a concrete circuit.

## Dependencies and notation

Plonkish arithmetization depends on a field over a prime modulus $p$. Integers taken modulo the field modulus $p$ are called field elements and their type is denoted as $\F$; arithmetic operations on field elements are implicitly performed modulo $p$. We denote the additive identity by $0$ and the multiplicative identity by $1$.  We denote the sum, difference, and product of two field elements using the $+$, $-$, and $\cdot$ operators, respectively.

$\N$ refers to the type of natural numbers, $\N^+$ to the type of positive integers, and $\Z$ to the type of integers.

The notation $\range{a}{b}$ means the vector of integers from $a$ (inclusive) to $b$ (exclusive) in ascending order.

The notation $x \typecolon T$ means that $x$ is of type $T$.

$T \times U$ means the type of pairs with first element from the type $T$, and second element from the type $U$.

$T \to U$ means the type of functions with range type $T$ and domain type $U$.

$[n]$ means the type of natural numbers from $0$ (inclusive) to $n$ (exclusive).

$T^{[m]}$ means the type of vectors indexed by $[m]$ with elements from type $T$.

$T^{[m \times n]}$ means the type of matrices indexed first by a column index in $[m]$ and then by a row index in $[n]$, with elements from type $T$. That is, if $w \typecolon T^{[m \times n]}$ then $w[i, j]$ means the element at column index $i \typecolon [m]$ and row index $j \typecolon [n]$.

If $X$ is a field element, on the other hand, then $X^e$ means the result of raising $X$ to the integer power $e$. There are no square brackets around the exponent in this case.

The length of a vector $S$, or the number of elements in a set $S$, is written $\#S$.

The condition that $e$ is a member of the set $S$ is written $e \in S$.

$\Set{T}$ means the type of sets with elements in $T$.

$\Equiv{T}$ means the type of equivalence relations (i.e. reflexive, symmetric, and transitive binary relations) on $T$.

$\vecof{f(e) \where e \gets \range{a}{b}}$ means the vector of evaluations of $f$ on $\range{a}{b}$.

$\vecof{f(e) \where e}$ means the vector of evaluations of $f$ for some implicitly defined vector of zero-based indices $e$.

$\sum\,S$ means the sum of a vector $S$ of field elements, and $\prod\,S$ means the product.

$\implies$ means logical implication.

When $f$ is a function that takes a tuple as argument, we will allow $f((i, j))$ to be written as $f[i, j]$.

The terminology used here is intended to be consistent with the [ZKProof Community Reference](https://docs.zkproof.org/reference). We diverge from this terminology as follows:
* We refer to the public inputs to the circuit as an "instance vector". The entries of this vector are called "instance variables" in the Community Reference.

## The General Plonkish Relation $\cR_\plonkish$

The general relation $\cR_\plonkish$ contains pairs of $(x, w)$ where:
* the instance $x$ consists of the parameters of the proof system, the circuit $C$, and the public inputs to the circuit (i.e. the instance vector).
* the witness $w$ consists of the matrix of values provided by the prover. In this model it consists of the (potentially private) prover inputs to the circuit, and any intermediate values (including fixed values) that are not inputs to the circuit but are required in order to satisfy it.

We say that a $x$ is a *valid* instance whenever there exists some witness $w$ such that $(x, w) \in \cR_\plonkish$ holds.
The Plonkish language $\cL_\plonkish$ contains all valid instances.

A circuit-specific relation is a specialization of $\cR_\plonkish$ to a particular circuit.

If the proof system is knowledge sound, then the prover must have knowledge of the witness in order to construct a valid proof. If it is also zero knowledge, then witness entries can be private, and an honestly generated proof leaks no information about the private inputs to the circuit beyond the fact that it was obtained with knowledge of some satisfying witness.

### Instances

The relation $\cR_\plonkish$ takes instances of the following form:

| $\sf{Instance}$ | $\bs\sf{element}$                  | Description                                                                                          |
| ---------------:|:---------------------------------- |:---------------------------------------------------------------------------------------------------- |
|            $\F$ |                                    | A prime field.                                                                                       |
|             $C$ |                                    | The circuit.                                                                                         |
|             $ϕ$ | $\oftype \F^{[C.t]}\hspace{4.5em}$ | The instance vector, where $C.t$ is the instance vector length defined below.                        |

The circuit $C \typecolon \AbstractCircuit_{\F}$ in turn has the following form:

|  $\sf{Circuit}$ | $\bs\sf{element}$                  | Description                                                                                          | Used in                                   |
| ---------------:|:---------------------------------- |:---------------------------------------------------------------------------------------------------- |:----------------------------------------- |
|             $t$ | $\oftype \N$                       | Length of the instance vector.                                                                       |                                           |
|             $n$ | $\oftype \N \where n > 0$          | Number of rows for the witness matrix.                                                               |                                           |
|             $m$ | $\oftype \N \where m > 0$          | Number of columns for the witness matrix.                                                            |                                           |
|        $\equiv$ | $\oftype \Equiv{[m] \times [n]}$   | An equivalence relation indicating which witness entries must be equal to each other.                | [Copy constraints](#copy-constraints)     |
|             $S$ | $\oftype ([m] \times [n])^{[t]}$   | A vector indicating which witness entries are equal to instance vector entries.                      | [Copy constraints](#copy-constraints)     |
|           $m_f$ | $\oftype \N \where m_f ≤ m$        | Number of columns that are fixed.                                                                    | [Fixed constraints](#fixed-constraints)   |
|             $f$ | $\oftype \F^{[m_f \times n]}$      | The fixed content of the first $m_f$ columns.                                                        | [Fixed constraints](#fixed-constraints)   |
|           $p_u$ | $\oftype \F^{[m]} \to \F$          | Custom multivariate polynomials.                                                                     | [Custom constraints](#custom-constraints) |
|        $\CUS_u$ | $\oftype \Set{[n]}$                | Sets indicating rows on which the custom polynomials $p_u$ are constrained to evaluate to $0$.       | [Custom constraints](#custom-constraints) |
|           $L_v$ | $\oftype \N$                       | Length of vectors in the lookup table with index $v$.                                                | [Lookup constraints](#lookup-constraints) |
|        $\TAB_v$ | $\oftype \Set{\F^{[L_v]}}$         | Lookup tables $\TAB_v$ each containing a set of vectors of type $\F^{[L_v]}$.                        | [Lookup constraints](#lookup-constraints) |
|       $q_{v,s}$ | $\oftype \F^{[m]} \to \F$          | Scaling multivariate polynomials $q_{v,s}$ for $s \typecolon [L_v]$.                                 | [Lookup constraints](#lookup-constraints) |
|       $\LOOK_v$ | $\oftype \Set{[n]}$                | Sets indicating rows on which the scaling polynomials $q_{v,s}$ evaluate to some vector in $\TAB_v$. | [Lookup constraints](#lookup-constraints) |

Multivariate polynomials are defined below in the [Custom constraints](#custom-constraints) section.

### Witnesses

The relation $\cR_\plonkish$ takes witnesses of the following form:

|  $\sf{Witness}$ | $\bs\sf{element}$                         | Description         |
| ---------------:|:----------------------------------------- |:------------------- |
|             $w$ | $\oftype \F^{[m \times n]}\hspace{4.1em}$ | The witness matrix. |

Define $\vec{w}_j$ as the row vector $\vecof{w[i, j] \where i \gets \range{0}{m}}$.

### Definition of the relation

Given the above definitions, the relation $\cR_\plonkish$ corresponds to a set of $\kern0.1em(\textsf{instance},\,\textsf{witness})\kern0.1em$ pairs $(x, w)$ where
$$
\left(x = \left(\F,\ C = \left(t, n, m, \kern-0.1em\equiv, S, m_f, f,\ \vecof{(p_u, \CUS_{u}) \where u}\!,\,\vecof{(L_v, \TAB_v, \vecof{q_{v,s} \where s}\!, \LOOK_v) \where v}\right)\!,\, ϕ\right)\!,\, w \right)
$$
such that:
$$
\begin{array}{ll|l}
   w \typecolon \F^{[m \times n]}\comma f \typecolon \F^{[m_f \times n]} & & i \typecolon [m_f]\comma j \typecolon [n] \implies w[i, j] = f[i, j] \\[0.3ex]
   S \typecolon ([m] \times [n])^{[t]}\comma ϕ \typecolon \F^{[t]} & & k \typecolon [t] \implies w[S[k]] = ϕ[k] \\[0.3ex]
   \equiv\,\,\typecolon \Equiv{[m] \times [n]} & & (i,j) \equiv (k,\ell) \implies w[i, j] = w[k, \ell] \\[0.3ex]
   \CUS_u \typecolon \Set{[n]}\comma p_u \typecolon \F^{[m]} \to \F & & j \in \CUS_u \implies p_u(\vec{w}_j) = 0 \\[0.3ex]
   \LOOK_v \typecolon \Set{[n]}\comma q_{v,s} \typecolon \F^{[m]} \to \F\comma \TAB_v \typecolon \Set{\F^{[L_v]}} & & j \in \LOOK_v \implies \vecof{q_{v,s}(\vec{w}_j) \where s \gets \range{0}{L_v}} \in \TAB_v
\end{array}
$$

In this model, a circuit-specific relation $\cR_{\F, C}$ for a field $\F$ and circuit $C$ is the relation $\cR_\plonkish$ restricted to the subset of instances and witnesses $((\F, C, ϕ \typecolon \F^{[C.t]}),\ w \typecolon \F^{[C.m \times C.n]})$.

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

| Copy Constraints                                        | Description                                                                                       |
| ------------------------------------------------------- |:------------------------------------------------------------------------------------------------- |
| $k \typecolon [t] \implies$ $w[S[k]] = ϕ[k]$            | The instance entry at index $k$ is equal to the advice entry at location $(i,j) = S[k]$.          |
| $(i,j) \equiv (k,\ell) \implies$ $w[i, j] = w[k, \ell]$ | $\equiv$ is an equivalence relation indicating which witness entries are constrained to be equal. |

By convention, when fixed abstract cells have the same value, we consider them to be equivalent under $\equiv$. That is,

$i < m_f$ and $k < m_f$ and $f[i, j] = f[k, \ell] \implies (i, j) \equiv (k, \ell)$

This has no direct effect on the relation, but it will simplify expressing an [optimization](optimizations.md).

#### Custom constraints

Plonkish also allows custom constraints between the witness matrix entries. In the abstract model we are defining, a custom constraint applies only within a single row of the witness matrix, for the rows that are selected for that constraint.

In some systems using Plonkish, custom constraints are referred to as "gates".

Custom constraints enforce that witness entries within a row satisfy some multivariate polynomial. Here $p_u$ could indicate any case that can be generated using a combination of multiplications and additions.

| Custom Constraints | Description |
| ------------------ |:----------- |
| $j \in \CUS_u \implies$ $p_u(\vec{w}_j) = 0$ | $u$ is the index of a custom constraint. $j$ ranges over the set of rows $\CUS_u$ for which the custom constraint is switched on. |

Here $p_u \typecolon \F^{[m]} \to \F$ is an arbitrary [multivariate polynomial](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)):

> Given $\eta$ symbols $X_i$ for $i \typecolon [\eta]$ called indeterminates, a multivariate polynomial $P$ in these indeterminates with coefficients in $\F$ is a finite linear combination
>
> $$P\!\left(\vecof{X_b \where b \gets \range{0}{\eta}}\right) = \sum_{z \stypecolon [\nu]} \Big(c_z \cdot \prod_{b \stypecolon [\eta]} X_b^{\alpha_{z,b}}\Big)$$
>
> where $c_z \typecolon \F\comma$ $c_z \neq 0\comma$ and $\nu$ and $\alpha_{z,b}$ are positive integers.

#### Lookup constraints

Lookup constraints enforce that some polynomial function of the witness entries on a row are contained in some table.

The sizes of tables are not limited at this layer. A realization of a proving system using Plonkish arithmetization may limit the supported size of tables, possibly depending on $n$, or it may have some way to compile larger tables.

In this specification, we only support fixed lookup tables determined in advance. This could be generalized to support dynamic tables determined by part of the witness matrix.

| Lookup Constraints | Description |
| ------------------ |:----------- |
| $j \in \LOOK_v \implies$ $\vecof{q_{v,s}(\vec{w}_j) \where s \gets \range{0}{L_v}} \in \TAB_v$ | $v$ is the index of a lookup table. $j$ ranges over the set of rows $\LOOK_v$ for which the lookup constraint is switched on. |

Here $\vecof{q_{v,s} \typecolon \F^{[m]} \to \F \where s \gets \range{0}{L_v}}$ are multivariate polynomials that collectively map the witness entries $\vec{w}_j$ on the lookup row $j \in \LOOK_v$ to a tuple of field elements. This tuple will be constrained to match some row of the table $\TAB_v$.
