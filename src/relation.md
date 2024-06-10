# Specification of the Plonkish Relation

## Objectives
- Need to agree on the API between “zkInterface for Plonkish” and the proving system.  Specify a general statement that the proving system has to implement.
- Section 2 of [[Thomas 2022]](https://eprint.iacr.org/2022/777.pdf) : describes high level API of zk Interface for Plonkish statements

This is intended to be read in conjunction with the [Plonkish Backend Optimizations](optimizations.md) document, which describes how to compile the abstract constraint system described here into a concrete circuit.

## Dependencies and notation

Plonkish arithmetisation depends on a scalar field over a prime modulus $p$. We represent this field as the object $\mathbb{F}$. We denote the additive identity by $0$ and the multiplicative identity by $1$. Integers, taken modulo the field modulus $p$, are called scalars; arithmetic operations on scalars are implicitly performed modulo $p$. We denote the sum, difference, and product of two scalars using the $+$, $-$, and $*$ operators, respectively.

The notation $a \text{..} b$ means the sequence of integers from $a$ (inclusive) to $b$ (exclusive) in ascending order. $[a, b)$ means the corresponding set of integers. $[f(x) : x \leftarrow a \text{..} b]$ means the sequence of evaluations of $f$ on $a \text{..} b$.

## The Plonkish Relation $\mathcal{R}_{\mathsf{plonkish}}$

The relation $\mathcal{R}_{\mathsf{plonkish}}$ contains pairs of instances $\mathsf{instance}$, and witnesses $w$.

We say that $\mathsf{instance}$ is a valid instance whenever there exists some advice $w$ such that $(\mathsf{instance}, w) \in \mathcal{R}_{\mathsf{plonkish}}.$
The Plonkish language $\mathcal{L}_{\mathsf{plonkish}}$ contains all valid instances.

If the proof system is knowledge sound, then the prover must have knowledge of the witness in order to construct a valid proof. In the setting of a zero-knowledge proof system, the witness is private and the proof leaks no additional information about it.

### Instances

The relation $\mathcal{R}_{\mathsf{plonkish}}$ takes instances of the following form:

| Instance element  | Description |
| ----------------- | -------- |
| $\mathbb{F}$      | A prime field. |
| $t$               | Number of instance entries. |
| $\phi$            | Instance entries $\phi \mathrel{⦂} \mathbb{F}^t$. |
| $n > 0$           | Number of rows. |
| $m$               | Number of columns. |
| $\equiv$          | An equivalence relation on $[0,m) \times [0,n)$ indicating which advice entries are equal. |
| $S$               | A set $S \subseteq ([0,m) \times [0,n)) \times [0,t)$ indicating which instance entries must be used in the advice. |
| $m_f \leq m$      | Number of columns that are fixed. |
| $f$               | The fixed content of the first $m_f$ columns, $f \mathrel{⦂} \mathbb{F}^{m_f \times n}$. |
| $\mathsf{CUS}_u$  | Sets $\mathsf{CUS}_u \subseteq [0,n)$ indicating which rows the custom functions $p_u \mathrel{⦂} \mathbb{F}^{m} \mapsto \mathbb{F}$ are applied to. |
| $p_u$             | Custom multivariate polynomials $p_u \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}$. |
| $L_v$             | Number of table columns in each lookup table $\mathsf{TAB}_v$. |
| $\mathsf{LOOK}_v$ | Sets $\mathsf{LOOK}_v \subseteq [0,n)$ indicating which rows the scaled lookups into $\mathsf{TAB}_v$ are applied to. |
| $q_{v,s}$         | Custom scaling functions $q_{v,s} \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}$ for $s \leftarrow 0 \text{..} L_v$. |
| $\mathsf{TAB}_v$  | Lookup tables $\mathsf{TAB}_v \subseteq \mathbb{F}^{L_v}$, each with a number of tuples in $\mathbb{F}^{L_v}$. |

> TODO: do we need to generalise lookup tables to support dynamic tables (in advice columns)? Probably too early, but we could think about it.

### Witnesses

The relation $\mathcal{R}_{\mathsf{plonkish}}$ takes a witness of the following form:

| Witness           | Description |
| ----------------- | -------- |
| $w$               | Columns $w \mathrel{⦂} \mathbb{F}^{m \times n}$. |

Define $\vec{w}_j$ as the row vector $[w[i, j] : i \leftarrow 0 \text{..} m]$.

### Definition of the relation

Given the above definitions, the relation $\mathcal{R}_{\mathsf{plonkish}}$ is given by:

$$
\left\{ \begin{array}{cc | c}
   (\mathbb{F}, t, \phi, n, m, \equiv, S, m_f, f, \{\mathsf{CUS}_{u}, p_u\}_u, \{ L_v, \mathsf{LOOK}_v, \{ q_{v,s} \}_s, \mathsf{TAB}_v \}), & & - \\
   f \mathrel{⦂} \mathbb{F}^{m_f \times n}, \ w \mathrel{⦂} \mathbb{F}^{m \times n} & & i \in [0,m_f), \ j \in [0,n) \Rightarrow w[i, j] = f[i, j] \\
   S \subseteq ([0,m) \times [0,n)) \times [0,t), \ \phi \mathrel{⦂} \mathbb{F}^t & & ((i,j),k) \in S \Rightarrow w[i, j] = \phi[k] \\
   \equiv\; \subseteq ([0,m) \times [0,n)) \times ([0,m) \times [0,n)) & & (i,j) \equiv (k,\ell) \Rightarrow w[i, j] = w[k, \ell] \\
   \mathsf{CUS}_u \subseteq [0,n), \ p_u \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F} & & j \in \mathsf{CUS}_u \Rightarrow p_u(\vec{w}_j) = 0 \\
   \mathsf{LOOK}_v \subseteq [0,n), \ q_{v,s} \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}, \ \mathsf{TAB}_v \subseteq \mathbb{F}^{L_v} & & j \in \mathsf{LOOK}_v \Rightarrow [q_{v,s}(\vec{w}_j) : s \leftarrow 0 \text{..} L_v] \in \mathsf{TAB}_v
\end{array} \right\}
$$

### Conditions satisfied by statements in $\mathcal{R}_{\mathsf{plonkish}}$

There are four types of constraints that a Plonkish statement $(\mathsf{instance}, w) \in \mathcal{R}_{\mathsf{Plonkish}}$ must satisfy:

* Fixed constraints
* Copy constraints
* Custom constraints
* Lookup constraints

#### Fixed constraints

The first $m_f$ columns of $w$ are fixed to the columns of $f$.

#### Copy constraints

Copy constraints that enforce that advice entries must be equal to other inputs.  Plonkish allows custom constraints between the instance, fixed, and advice constraint entries.

| Copy Constraints  | Description |
| ----------------- | -------- |
| $((i,j),k) \in S \Rightarrow w[i, j] = \phi[k]$ | The $(i,j)$ th advice entry is equal to the $k$ th instance entry for all $((i,j),k) \in S$. |
| $(i,j) \equiv (k,\ell) \Rightarrow w[i, j] = w[k, \ell]$ | $\equiv$ is an equivalence relation indicating which advice entries are constrained to be equal. |

#### Custom constraints

Custom constraints that enforce that fixed entries and advice entries satisfy some multivariate polynomial. Here $p_u$ could indicate a multiplication gate, an addition gate, or any other custom case that can be generated using a combination of multiplication gates and addition gates.

| Custom Constraints | Description |
| -------- | -------- | 
| $j \in \mathsf{CUS}_u \Rightarrow p_u(\vec{w}_j) = 0$ | $u$ is the index of a custom constraint. $j$ ranges over the set of rows $\mathsf{CUS}_u$ for which the custom constraint is switched on. |

Here $p_u \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}$ is an arbitrary [multivariate polynomial](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)):

> Given $\eta$ symbols $X_0, \dots, X_{\eta-1}$ called indeterminates, a multivariate polynomial $P$ in these indeterminates, with coefficients in $\mathbb{F}$,
> is a finite linear combination $$P(X_0, \dots, X_{\eta-1}) = \sum_{z=0}^{\nu-1} \Big(c_z\, {\small\prod_{b=0}^{\eta-1}}\, X_b^{\alpha_{z,b}}\Big)$$ where $\nu \mathrel{⦂} \mathbb{N}$, $c_z \mathrel{⦂} \mathbb{F}$, and $\alpha_{z,b} \mathrel{⦂} \mathbb{N}$.

#### Lookup constraints

Lookup constraints enforce that advice entries are contained in some table.

The sizes of tables are not limited at this layer. A realization of a proving system using Plonkish arithmetization may limit the supported size of tables, possibly depending on $n$, or it may have some way to compile larger tables.

Fixed lookup tables are determined in advance. Dynamic lookup tables would be determined by the advice, but are not supported in this version.

| Lookup Constraints | Description |
| -------- | -------- |
| $j \in \mathsf{LOOK}_v \Rightarrow [q_{v,s}(\vec{w}_j) : s \leftarrow 0 \text{..} L_v] \in \mathsf{TAB}_v$ | $v$ is the index of a lookup table. $j$ ranges over the set of rows $\mathsf{LOOK}_v$ for which the lookup constraint is switched on. |

Here $q_{v,s} \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}$ for $s \leftarrow 0 \text{..} L_v$ are multivariate polynomials that collectively map the fixed and advice cells $\vec{w}_j$ on the lookup row $j \in \mathsf{LOOK}_v$ to a tuple of field elements. This tuple will be constrained to match some row of the table $\mathsf{TAB}_v$.
