# Specification of the Plonkish Relation

## Objectives
- Need to agree on the API between “zkInterface for Plonkish” and the proving system.  Specify a general statement that the proving system has to implement.
- Section 2 of [[Thomas 2022]](https://eprint.iacr.org/2022/777.pdf) : describes high level API of zk Interface for Plonkish statements

This is intended to be read in conjunction with the [Plonkish Backend Optimizations](optimizations.md) document, which describes how to compile the abstract constraint system described here into a concrete circuit.

## Dependencies and notation

Plonkish arithmetisation depends on a scalar field over a prime modulus $p$. We represent this field as the object $\mathbb{F}$. We denote the additive identity by $0$ and the multiplicative identity by $1$. Integers, taken modulo the field modulus $p$, are called scalars; arithmetic operations on scalars are implicitly performed modulo $p$. We denote the sum, difference, and product of two scalars using the $+$, $-$, and $*$ operators, respectively.

The notation $a \text{..} b$ means the sequence of integers from $a$ (inclusive) to $b$ (exclusive) in ascending order. $[a, b)$ means the corresponding set of integers.

$\big\{\, f(e) : e \in S \,\big\}$ means the set of evaluations of $f$ on the set $S$.

$\big[\, f(e) : e \leftarrow a \text{..} b \,\big]$ means the sequence of evaluations of $f$ on $a \text{..} b$.

$\big[\, A_e \,\big]_e$ means the sequence of $A_e$ for some implicitly defined sequence of indices $e$.

The terminology used here is intended to be consistent with the [ZKProof Community Reference](https://docs.zkproof.org/reference). We diverge from this terminology as follows:
* We refer to the public inputs to the circuit as an "instance vector". The entries of this vector are called "instance variables" in the Community Reference.

## The Plonkish Relation $\mathcal{R}_{\mathsf{plonkish}}$

The relation $\mathcal{R}_{\mathsf{plonkish}}$ contains pairs of $(x, w)$ where:
* the instance $x$ consists of the parameters of the proof system, the circuit, and the public inputs to the circuit (i.e. the instance vector).
* the witness $w$ consists of the matrix of values provided by the prover. In this model it consists of the (potentially private) prover inputs to the circuit, and any intermediate values (including fixed values) that are not inputs to the circuit but are required in order to satisfy it.

We say that a $x$ is a *valid* instance whenever there exists some witness $w$ such that $(x, w) \in \mathcal{R}_{\mathsf{plonkish}}$ holds.
The Plonkish language $\mathcal{L}_{\mathsf{plonkish}}$ contains all valid instances.

If the proof system is knowledge sound, then the prover must have knowledge of the witness in order to construct a valid proof. If it is also zero knowledge, then witness entries can be private, and an honestly generated proof leaks no information about the private inputs to the circuit beyond the fact that it was obtained with knowledge of some satisfying witness.

### Instances

The relation $\mathcal{R}_{\mathsf{plonkish}}$ takes instances of the following form:

| Instance element  | Description |
| ----------------- | -------- |
| $\mathbb{F}$      | A prime field. |
| $t$               | Length of the instance vector. |
| $\phi$            | The instance vector $\phi \mathrel{⦂} \mathbb{F}^t$. |
| $n > 0$           | Number of rows. |
| $m > 0$           | Number of columns. |
| $\equiv$          | An equivalence relation on $[0,m) \times [0,n)$ indicating which witness entries are equal to each other. |
| $S$               | A set $S \subseteq ([0,m) \times [0,n)) \times [0,t)$ indicating which witness entries are equal to instance vector entries. |
| $m_f \leq m$      | Number of columns that are fixed. |
| $f$               | The fixed content of the first $m_f$ columns, $f \mathrel{⦂} \mathbb{F}^{m_f \times n}$. |
| $p_u$             | Custom multivariate polynomials $p_u \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}$. |
| $\mathsf{CUS}_u$  | Sets $\mathsf{CUS}_u \subseteq [0,n)$ indicating rows on which the custom polynomials $p_u$ are constrained to evaluate to 0. |
| $L_v$             | Number of table columns in each lookup table $\mathsf{TAB}_v$. |
| $\mathsf{TAB}_v$  | Lookup tables $\mathsf{TAB}_v \subseteq \mathbb{F}^{L_v}$, each with a number of tuples in $\mathbb{F}^{L_v}$. |
| $q_{v,s}$         | Scaling multivariate polynomials $q_{v,s} \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}$ for $s \leftarrow 0 \text{..} L_v$. |
| $\mathsf{LOOK}_v$ | Sets $\mathsf{LOOK}_v \subseteq [0,n)$ indicating rows on which the scaling polynomials $q_{v,s}$ evaluate to some tuple in $\mathsf{TAB}_v$. |

### Witnesses

The relation $\mathcal{R}_{\mathsf{plonkish}}$ takes witnesses of the following form:

| Witness element   | Description |
| ----------------- | -------- |
| $w$               | The witness matrix $w \mathrel{⦂} \mathbb{F}^{m \times n}$. |

Define $\vec{w}_j$ as the row vector $\big[\, w[i, j] : i \leftarrow 0 \text{..} m \,\big]$.

### Definition of the relation

Given the above definitions, the relation $\mathcal{R}_{\mathsf{plonkish}}$ corresponds to a set of $\,(\!$ instance $\!,\,$ witness $\!)\,$ pairs
$$
\Big(x = \big(\mathbb{F}, t, \phi, n, m, \equiv, S, m_f, f, \big[\, (p_u, \mathsf{CUS}_{u}) \,\big]_u, \big[\, (L_v, \mathsf{TAB}_v, \big[\, q_{v,s} \,\big]_s, \mathsf{LOOK}_v) \,\big]_v\big),\, w \Big)
$$
such that:
$$
\begin{array}{ll|l}
   w \mathrel{⦂} \mathbb{F}^{m \times n}, \ f \mathrel{⦂} \mathbb{F}^{m_f \times n} & & i \in [0,m_f), \ j \in [0,n) \Rightarrow w[i, j] = f[i, j] \\[0.3ex]
   S \subseteq ([0,m) \times [0,n)) \times [0,t), \ \phi \mathrel{⦂} \mathbb{F}^t & & ((i,j),k) \in S \Rightarrow w[i, j] = \phi[k] \\[0.3ex]
   \equiv\; \subseteq ([0,m) \times [0,n)) \times ([0,m) \times [0,n)) & & (i,j) \equiv (k,\ell) \Rightarrow w[i, j] = w[k, \ell] \\[0.3ex]
   \mathsf{CUS}_u \subseteq [0,n), \ p_u \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F} & & j \in \mathsf{CUS}_u \Rightarrow p_u(\vec{w}_j) = 0 \\[0.3ex]
   \mathsf{LOOK}_v \subseteq [0,n), \ q_{v,s} \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}, \ \mathsf{TAB}_v \subseteq \mathbb{F}^{L_v} & & j \in \mathsf{LOOK}_v \Rightarrow \big[\, q_{v,s}(\vec{w}_j) : s \leftarrow 0 \text{..} L_v \,\big] \in \mathsf{TAB}_v
\end{array}
$$

### Conditions satisfied by statements in $\mathcal{R}_{\mathsf{plonkish}}$

There are four types of constraints that a Plonkish statement $(x, w) \in \mathcal{R}_{\mathsf{Plonkish}}$ must satisfy:

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
| $((i,j),k) \in S \Rightarrow w[i, j] = \phi[k]$ | The $(i,j)$ th advice entry is equal to the $k$ th instance entry for all $((i,j),k) \in S$. |
| $(i,j) \equiv (k,\ell) \Rightarrow w[i, j] = w[k, \ell]$ | $\equiv$ is an equivalence relation indicating which witness entries are constrained to be equal. |

By convention, when fixed abstract cells have the same value, we consider them to be equivalent under $\equiv$. That is,
$$
i < m_f \;\wedge\; k < m_f \;\wedge\; f[i, j] = f[k, \ell] \Rightarrow (i, j) \equiv (k, \ell)
$$
This has no direct effect on the relation, but it will simplify expressing an [optimization](optimizations.md).

#### Custom constraints

Plonkish also allows custom constraints between the witness matrix entries. In the abstract model we are defining, a custom constraint applies only within a single row of the witness matrix, for the rows that are selected for that constraint.

In some systems using Plonkish, custom constraints are referred to as "gates".

Custom constraints enforce that witness entries within a row satisfy some multivariate polynomial. Here $p_u$ could indicate any case that can be generated using a combination of multiplications and additions.

| Custom Constraints | Description |
| -------- | -------- | 
| $j \in \mathsf{CUS}_u \Rightarrow p_u(\vec{w}_j) = 0$ | $u$ is the index of a custom constraint. $j$ ranges over the set of rows $\mathsf{CUS}_u$ <br> for which the custom constraint is switched on. |

Here $p_u \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}$ is an arbitrary [multivariate polynomial](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)):

> Given $\eta$ symbols $X_0, \dots, X_{\eta-1}$ called indeterminates, a multivariate polynomial $P$ in these indeterminates, with coefficients in $\mathbb{F}$,
> is a finite linear combination $$P(X_0, \dots, X_{\eta-1}) = \sum_{z=0}^{\nu-1} \Big(c_z\, {\small\prod_{b=0}^{\eta-1}}\, X_b^{\alpha_{z,b}}\Big)$$ where $\nu \mathrel{⦂} \mathbb{N}$, $c_z \mathrel{⦂} \mathbb{F}$, and $\alpha_{z,b} \mathrel{⦂} \mathbb{N}$.

#### Lookup constraints

Lookup constraints enforce that some polynomial function of the witness entries on a row are contained in some table.

The sizes of tables are not limited at this layer. A realization of a proving system using Plonkish arithmetization may limit the supported size of tables, possibly depending on $n$, or it may have some way to compile larger tables.

In this specification, we only support fixed lookup tables determined in advance. This could be generalized to support dynamic tables determined by part of the witness matrix.

| Lookup Constraints | Description |
| -------- | -------- |
| $j \in \mathsf{LOOK}_v \Rightarrow \big[\, q_{v,s}(\vec{w}_j) : s \leftarrow 0 \text{..} L_v \,\big] \in \mathsf{TAB}_v$ | $v$ is the index of a lookup table. $j$ ranges over the set of rows $\mathsf{LOOK}_v$ <br> for which the lookup constraint is switched on. |

Here $q_{v,s} \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}$ for $s \leftarrow 0 \text{..} L_v$ are multivariate polynomials that collectively map the witness entries $\vec{w}_j$ on the lookup row $j \in \mathsf{LOOK}_v$ to a tuple of field elements. This tuple will be constrained to match some row of the table $\mathsf{TAB}_v$.
