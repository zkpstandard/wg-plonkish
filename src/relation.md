# Specification of the Plonkish Relation

## Objectives
- Need to agree on the API between “zkInterface for Plonkish” and the proving system.  Specify a general statement that the proving system has to implement.
- Section 2 of [[Thomas 2022]](https://eprint.iacr.org/2022/777.pdf) : describes high level API of zk Interface for Plonkish statements

This is intended to be read in conjunction with the [Plonkish Backend Optimizations](optimizations.md) document, which describes how to compile the abstract constraint system described here into a concrete circuit.

## Dependencies

Plonkish arithmetisation depends on a scalar field over a prime modulus $p$. We represent this field as the object $\mathbb{F}$. We denote the additive identity by $0$ and the multiplicative identity by $1$. Integers, taken modulo the field modulus $p$, are called scalars; arithmetic operations on scalars are implicitly performed modulo $p$. We denote the sum, difference, and product of two scalars using the $+$, $-$, and $*$ operators, respectively.

## The Plonkish Relation
The relation $\mathcal{R}_{\mathsf{plonkish}}$ contains pairs of public instances $\mathsf{instance}$ and private advice $w$.
We say that $\mathsf{instance}$ is a valid instance whenever there exists some advice $w$ such that $(\mathsf{instance}, w) \in \mathcal{R}_{\mathsf{plonkish}}.$
The Plonkish language $\mathcal{L}_{\mathsf{plonkish}}$ contains all valid instances.

The relation $\mathcal{R}_{\mathsf{plonkish}}$ takes, as public inputs, instances of the form
$$
\mathsf{instance} = (\mathbb{F}, \phi, f, \equiv_A, S_I, \{ \mathsf{CUS}_{u}, p_u \}_u, \{ \mathsf{LOOK}_v, \mathsf{TAB}_v \}_v)
$$

### Inputs into $\mathcal{R}_{\mathsf{plonkish}}$

| Public Inputs     | Description |
| ----------------- | -------- |
| $\mathbb{F}$      | A prime field. |
| $t_I$             | Number of instance entries. |
| $\phi$            | Instance entries $\phi : \mathbb{F}^{t_I}$. |
| $n > 0$           | Number of rows. |
| $S_I$             | A set $S_I \subseteq ([0,m_A) \times [0,n)) \times [0,t_I)$ indicating which instance entries must be used in the advice. |
| $m_F$             | Number of fixed columns. |
| $f$               | Fixed columns $f : \mathbb{F}^{m_F \times n}$. |
| $S_F$             | A set $S_F \subseteq ([0,m_A) \times [0,n)) \times ([0,m_F) \times [0,n))$ indicating which fixed entries must be used in the advice. |
| $m_A > 0$         | Number of advice columns. |
| $\equiv_A$        | An equivalence relation on $[0,m_A) \times [0,n)$ indicating which advice entries are equal. |
| $\mathsf{CUS}_u$  | Sets $\mathsf{CUS}_u \subseteq [0,n)$ indicating which rows the custom functions $p_u: \mathbb{F}^{m_F + m_A} \mapsto \mathbb{F}$ are applied to. |
| $p_u$             | Custom multivariate polynomials $p_u: \mathbb{F}^{m_F + m_A}  \mapsto \mathbb{F}$. |
| $L_v$             | Number of table columns in each lookup table $\mathsf{TAB}_v$. |
| $\mathsf{LOOK}_v$ | Sets $\mathsf{LOOK}_v \subseteq [0,n)$ indicating which rows the scaled lookups $q_v(\text{fixed and advice entries on row } j) \in \mathsf{TAB}_v$ are applied to. |
| $q_v$             | Custom scaling functions $q_v: \mathbb{F}^{m_F + m_A} \mapsto \mathbb{F}^{L_v}$. |
| $\mathsf{TAB}_v$  | Lookup tables $\mathsf{TAB}_v \subseteq \mathbb{F}^{L_v}$, each with a number of tuples in $\mathbb{F}^{L_v}$. |

> TODO: do we need to generalise lookup tables to support dynamic tables (in advice columns)? Probably too early, but we could think about it.

| Private Inputs    | Description |
| ----------------- | -------- |
| $w$               | Advice columns $w : \mathbb{F}^{m_A \times n}$. |

Define $\mathsf{ROW}_j$ as the vector $[f[0, j], \ldots, f[m_F-1, j], w[0, j], \ldots, w[m_A-1,j]]$.

Given the above definitions, the relation $\mathcal{R}_{\mathsf{plonkish}}$ is given by:

$$
\left\{ \begin{array}{cc | c}
   (\mathbb{F}, (f, \phi), \equiv_A, S_I, \{\mathsf{CUS}_{u}, p_u\}_u, \{ \mathsf{LOOK}_v, \mathsf{TAB}_v, q_v \}), & & - \\
   f \in \mathbb{F}^{m_F \times n}, w \in \mathbb{F}^{m_A \times n}, \phi \in \mathbb{F}^{t_I} & & - \\
   S_I \subset ([0,m_A) \times [0,n)) \times [0,t_I) & & ((i,j),k) \in S_I \Rightarrow w[i, j] = \phi[k] \\
   S_F \subset ([0,m_A) \times [0,n)) \times ([0,m_F) \times [0,n)) & & ((i,j),(k,\ell)) \in S_F \Rightarrow w[i, j] = f[k, \ell] \\
   \equiv_A \subset ([0,m_A) \times [0,n)) \times ([0,m_A) \times [0,n)) & & (i,j) \equiv_A (k,\ell) \Rightarrow w[i, j] = w[k, \ell] \\
   \forall u, \ \mathsf{CUS}_u \subset [0,n), \ p_u: \mathbb{F}^{m_F + m_A} \mapsto \mathbb{F} & & j \in \mathsf{CUS}_u \Rightarrow p_u(\mathsf{ROW}_j) = 0 \\
   \mathsf{LOOK}_v \subset [0,n), \mathsf{TAB}_v \subset \mathbb{F}^{L_v} & & j \in \mathsf{LOOK}_v \Rightarrow q_v(\mathsf{ROW}_j) \in \mathsf{TAB}_k
\end{array} \right\}
$$

### Conditions satisfied by statements in $\mathcal{R}_{\mathsf{plonkish}}$

There are three types of constraints that a Plonkish statement $(\mathsf{instance}, w) \in \mathcal{R}_{\mathsf{Plonkish}}$ must satisfy:

* Copy constraints
* Custom constraints
* Lookup constraints

#### Copy constraints

Copy constraints that enforce that advice entries must be equal to other inputs.  Plonkish allows custom constraints between the instance, fixed, and advice constraint entries.

| Copy Constraints  | Description |
| ----------------- | -------- |
| $((i,j),k) \in S_I \Rightarrow w[i, j] = \phi[k]$ | The $k$th instance entry is equal to the $(i,j)$th advice entry for all $((i,j),k) \in S_I$. |
| $((i,j),(k,\ell)) \in S_F \Rightarrow w[i, j] = f[k, \ell]$ | The $(k, \ell)$th fixed entry is equal to the $(i,j)$th advice entry for all $((i,j),(k,\ell)) \in S_F$. |
| $(i,j) \equiv_A (k,\ell) \Rightarrow w[i, j] = w[k, \ell]$ | $\equiv_A$ is an equivalence relation indicating which advice entries are constrained to be equal. |

#### Custom constraints

Custom constraints that enforce that fixed entries and advice entries satisfy some multivariate polynomial.  Here $p_u$ could indicate a multiplication gate, an addition gate, or any other custom case that can be generated using a combination of multiplication gates and addition gates.

| Custom Constraints | Description |
| -------- | -------- | 
| $j \in \mathsf{CUS}_u \Rightarrow p_u(\mathsf{ROW}_j) = 0$ | $u$ is the index of a custom constraint. $j$ ranges over the set of rows $\mathsf{CUS}_u$ for which the custom constraint is switched on. |

<!---
Define the X notation earlier and use it throughout.
-->

Here $p_u: \mathbb{F}^{m_F + m_A} \mapsto \mathbb{F}$ is an arbitrary [multivariate polynomial](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)):

> Given $\eta$ symbols $X_1, \dots, X_\eta$ called indeterminates, a multivariate polynomial $p$ in these indeterminates, with coefficients in $\mathbb{F}$,
> is a finite linear combination $$p(X_1, \dots, X_\eta) = \sum_{i=1}^\nu c_i X_1^{\alpha_{i,1}}\cdots X_\eta^{\alpha_{i,\eta}}$$ where $\nu \in \mathbb{N}$, $c_i$ in $\mathbb{F}$, and $\alpha_{i,j} \in \mathbb{N}$.

#### Lookup constraints

Lookup constraints enforce that advice entries are contained in some table.

The sizes of tables are not constrained at this layer. A realization of a proving system using Plonkish arithmetization may limit the supported size of tables, for example limiting the number of entries in a given table depending on $n$, or it may have some way to compile larger tables.

Fixed lookup tables are determined in advance. Dynamic lookup tables would be determined by the advice, but are not supported in this version.

| Lookup Constraints | Description |
| -------- | -------- |
| $j \in \mathsf{LOOK}_v \Rightarrow q_v(\mathsf{ROW}_j) \in \mathsf{TAB}_v$ | $v$ is the index of a lookup table. $j$ ranges over the set of rows $\mathsf{LOOK}_v$ for which the lookup constraint is switched on. |

Here $q_v: \mathbb{F}^{m_F + m_A} \mapsto \mathbb{F}^{L_v}$ is a multivariate polynomial that maps the fixed and advice cells $\mathsf{ROW}_j$ on the lookup row $j \in \mathsf{LOOK}_v$ to a tuple of field elements that must match a row of the table $\mathsf{TAB}_v$.
