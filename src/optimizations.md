# Plonkish Backend Optimizations

## Background

The relation described in [Specification of the Plonkish Relation](relation.md) gives an abstract model of a Plonkish constraint system that is sufficiently expressive, but does not take into account some of the optimizations that are commonly used in Plonkish implementations, such as the use of offsets/rotations in Plonkish custom constraints.

The benefit of the simpler abstract model is that it allows reasoning about the circuit without needing to be concerned with layout of the witness matrix, i.e. the position of rows relative to each other. The drawback of using only the abstract model, is that it may require a greater number of columns to express a given circuit than a model that supports offsets. This directly affects proof size for popular instantiations of proof systems based on Plonkish.

In this document we specify a method to translate from an abstract circuit to a concrete one, that retains the zero-knowledge, (knowledge) soundness, and completeness of the abstract system. This can include automated optimizations, which are able to reorder the rows as needed without changing the meaning of the circuit.

The optimizations suggested in this specification would be impractical or error-prone to perform manually, as they require global reasoning about the witness layout. Without automation, ensuring correctness while reordering rows or applying offsets becomes fragile and difficult to scale, especially in the presence of copy constraints or lookups where subtle errors can silently break circuit soundness.

In this document, we:

* **Define the concrete Plonkish relation**, intended for readers building a proving system or interactive oracle proof targeting the concrete Plonkish relation.

* **Describe a correctness-preserving circuit translation**, for those verifying the optimizations introduced in this document.

* **Specify the translation from an abstract to a concrete Plonkish relation**, aimed at implementers of the concrete relation.

* **Prove that the translation preserves correctness**, again intended for readers verifying the soundness of the optimisations.

## The Concrete Plonkish Relation

The relation $\mathcal{R}_{\mathsf{concrete}}$ is an optimisation of $\mathcal{R}_{\mathsf{plonkish}}$.  We have highlighted differences using the icon ✨.

### Instances

$\mathcal{R}_{\mathsf{concrete}}$ takes instances of the following form:

| Instance element  | Description |
| ----------------- | ----------- |
| $\mathbb{F}$      | A prime field. |
| $C$               | The circuit. |
| $\phi$            | The instance vector $\phi \mathrel{⦂} \mathbb{F}^{C.t}$ (where $t$ is the instance vector length defined below). |

The circuit $C \mathrel{⦂} \mathsf{ConcreteCircuit}_{\mathbb{F}}$ in turn has the following form:

| Circuit element   | Description | Used in |
| ----------------- | ----------- | ------- |
| ✨ $d$                | Number of offsets.  |  |
| ✨ $\mathsf{offsets}$ | Set of offsets enabling optimisations on the circuit stucture| [Custom constraints](#custom-constraints), [Lookup constraints](#lookup-constraints)
| $t$               | Length of the instance vector. |  |
| $n > 0$           | Number of rows for the witness matrix. |  |
| $m > 0$           | Number of columns for the witness matrix. |  |
| $\equiv$          | An equivalence relation on $[0,m) \times [0,n)$ indicating which witness entries are equal to each other. | [Copy constraints](#copy-constraints) |
| $S$               | A set $S \subseteq ([0,m) \times [0,n)) \times [0,t)$ indicating which witness entries are equal to instance vector entries. | [Copy constraints](#copy-constraints) |
| $m_f \leq m$      | Number of columns that are fixed. | [Fixed constraints](#fixed-constraints) |
| $f$               | The fixed content of the first $m_f$ columns, $f \mathrel{⦂} \mathbb{F}^{m_f \times n}$. | [Fixed constraints](#fixed-constraints) |
| $p_u$             | ✨ Custom multivariate polynomials $p_u \mathrel{⦂} \mathbb{F}^{d  m} \rightarrow \mathbb{F}$. | [Custom constraints](#custom-constraints) |
| $\mathsf{CUS}_u$  | Sets $\mathsf{CUS}_u \subseteq [0,n)$ indicating rows on which the custom polynomials $p_u$ are constrained to evaluate to 0. | [Custom constraints](#custom-constraints) |
| $L_v$             | Number of table columns in the lookup table with index $v$, $\mathsf{TAB}_v$. | [Lookup constraints](#lookup-constraints) |
| $\mathsf{TAB}_v$  | Lookup tables $\mathsf{TAB}_v \subseteq \mathbb{F}^{L_v}$, each with a number of tuples in $\mathbb{F}^{L_v}$. | [Lookup constraints](#lookup-constraints) |
| $q_{v,s}$         | ✨ Scaling multivariate polynomials $q_{v,s} \mathrel{⦂} \mathbb{F}^{d  m} \rightarrow \mathbb{F}$ for $s \leftarrow 0 \text{..} L_v$. | [Lookup constraints](#lookup-constraints) |
| $\mathsf{LOOK}_v$ | Sets $\mathsf{LOOK}_v \subseteq [0,n)$ indicating rows on which the scaling polynomials $q_{v,s}$ evaluate to some tuple in $\mathsf{TAB}_v$. | [Lookup constraints](#lookup-constraints) |

Multivariate polynomials are defined below in the [Custom constraints](#custom-constraints) section.

### Witnesses

The relation $\mathcal{R}_{\mathsf{concrete}}$ takes witnesses of the following form:

| Witness element   | Description |
| ----------------- | -------- |
| $w$               | The witness matrix $w \mathrel{⦂} \mathbb{F}^{m \times n}$. |

✨ Define $\vec{w}_{j} \in \mathbb{F}^{m d}$ as the row vector $\big[\, w[i, j + \mathsf{offset}] : (i, \mathsf{offset}) \leftarrow (0 \text{..} m) \times \mathsf{offsets} \,\big]$.

### Definition of the relation

Given the above definitions, the relation $\mathcal{R}_{\mathsf{concrete}}$ corresponds to a set of $\,(\!$ instance $\!,\,$ witness $\!)\,$ pairs
$$
 \left(x = \left(\mathbb{F}, C = \left(d, \mathsf{offsets}, t, n, m, \equiv, S, m_f, f, \left[\, (p_u, \mathsf{CUS}_{u}) \,\right]_u, \left[\, (L_v, \mathsf{TAB}_v, \left[\, q_{v,s} \,\right]_s, \mathsf{LOOK}_v) \,\right]_v\right), \phi\right),\, w \right)
$$
such that:
$$
\begin{array}{ll|l}
   w \mathrel{⦂} \mathbb{F}^{m \times n}, \ f \mathrel{⦂} \mathbb{F}^{m_f \times n} & & i \in [0,m_f), \ j \in [0,n) \Rightarrow w[i, j] = f[i, j] \\[0.3ex]
   S \subseteq ([0,m) \times [0,n)) \times [0,t), \ \phi \mathrel{⦂} \mathbb{F}^t & & ((i,j),k) \in S \Rightarrow w[i, j] = \phi[k] \\[0.3ex]
   \equiv\; \subseteq ([0,m) \times [0,n)) \times ([0,m) \times [0,n)) & & (i,j) \equiv (k,\ell) \Rightarrow w[i, j] = w[k, \ell] \\[0.3ex]
   \mathsf{CUS}_u \subseteq [0,n), \ p_u \mathrel{⦂} \mathbb{F}^{d  m} \rightarrow \mathbb{F} & & j \in \mathsf{CUS}_u \Rightarrow p_u(\vec{w}_j) = 0 \\[0.3ex]
   \mathsf{LOOK}_v \subseteq [0,n), \ q_{v,s} \mathrel{⦂} \mathbb{F}^{d  m} \rightarrow \mathbb{F}, \ \mathsf{TAB}_v \subseteq \mathbb{F}^{L_v} & & j \in \mathsf{LOOK}_v \Rightarrow \big[\, q_{v,s}(\vec{w}_j) : s \leftarrow 0 \text{..} L_v \,\big] \in \mathsf{TAB}_v
\end{array}
$$

In this model, a circuit-specific relation $\mathcal{R}_{\mathbb{F}, C}$ for a field $\mathbb{F}$ and circuit $C$ is the relation $\mathcal{R}_{\mathsf{plonkish}}$ restricted to $\{ ((\mathbb{F}, C, \phi \mathrel{⦂} \mathbb{F}^{C.t}), w \mathrel{⦂} \mathbb{F}^{C.m \times C.n}) \}$.

### Conditions satisfied by statements in $\mathcal{R}_{\mathsf{plonkish}}$

There are four types of constraints that a Plonkish statement $(x, w) \in \mathcal{R}_{\mathsf{concrete}}$ must satisfy:

* Fixed constraints
* Copy constraints
* Custom constraints
* Lookup constraints

An Interactive Oracle Proof for an optimised Plonkish constraint system must demonstrate that all of these contraints are satisfied by $\,(\!$ instance $\!,\,$ witness $\!) \in \mathcal{R}_{\mathsf{concrete}}\,$

#### Fixed constraints

The first $m_f$ columns of $w$ are fixed to the columns of $f$.

#### Custom constraints

In the concrete model we define here, a custom constraint applies to a set of offset rows relative to each row selected for that constraint.

Custom constraints enforce that witness entries within a row satisfy some multivariate polynomial. Here $p_u$ could indicate any case that can be generated using a combination of multiplications and additions.

| Custom Constraints | Description |
| -------- | -------- |
| $j \in \mathsf{CUS}_u \Rightarrow p_u(\vec{w}_j) = 0$ | $u$ is the index of a custom constraint. $j$ ranges over the set of rows $\mathsf{CUS}_u$ <br> for which the custom constraint is switched on. |

Here $p_u \mathrel{⦂} \mathbb{F}^{d  m} \rightarrow \mathbb{F}$ is an arbitrary [multivariate polynomial](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)):

> Given $\eta$ symbols $X_0, \dots, X_{\eta-1}$ called indeterminates, a multivariate polynomial $P$ in these indeterminates, with coefficients in $\mathbb{F}$,
> is a finite linear combination
>
> $P(X_0, \dots, X_{\eta-1}) = \sum_{z=0}^{\nu-1} \Big(c_z\, {\small\prod_{b=0}^{\eta-1}}\, X_b^{\alpha_{z,b}}\Big)$
>
>  where $\nu \mathrel{⦂} \mathbb{N}$, $c_z \mathrel{⦂} \mathbb{F} \neq 0$, and $\alpha_{z,b} \mathrel{⦂} \mathbb{N}$.

#### Lookup constraints

Lookup constraints enforce that some polynomial function of the witness entries on a row are contained in some table.
In this specification, we only support fixed lookup tables determined in advance. This could be generalized to support dynamic tables determined by part of the witness matrix.

| Lookup Constraints | Description |
| -------- | -------- |
| $j \in \mathsf{LOOK}_v \Rightarrow \big[\, q_{v,s}(\vec{w}_j) : s \leftarrow 0 \text{..} L_v \,\big] \in \mathsf{TAB}_v$ | $v$ is the index of a lookup table. $j$ ranges over the set of rows $\mathsf{LOOK}_v$ <br> for which the lookup constraint is switched on. |

Here $q_{v,s} \mathrel{⦂} \mathbb{F}^{d  m} \rightarrow \mathbb{F}$ for $s \leftarrow 0 \text{..} L_v$ are multivariate polynomials that collectively map the witness entries $\vec{w}_j$ on the lookup row $j \in \mathsf{LOOK}_v$ to a tuple of field elements. This tuple will be constrained to match some row of the table $\mathsf{TAB}_v$.

## Notation

If not otherwise defined, variable names used here are consistent with [the relation description](relation.md).

We will use the convention that variables marked with a prime ($'$) refer to *concrete* column or row indices.

For brevity when referring to variables dependent on an abstract circuit such as $C.t$, we will omit the $C.$ and just refer to $t$ when $C$ is obvious from context.

Similarly, when referring to variables dependent on a concrete circuit such as $C'.t'$, we will omit the $C'.$ and just refer to $t'$ when $C'$ is obvious from context.

An "abstract cell" specifies an entry in the witness matrix $w$ of the abstract circuit. A "concrete cell" specifies an entry in the witness matrix $w'$ of the concrete circuit.

We will denote the witness value at column $i$ and row $j$ as $w[i, j]$.

We say that an abstract cell with coordinates $(i, j)$ is "constrained" if it appears in some copy, custom, or lookup constraint. More precisely, $\mathsf{constrained}[i, j]$ is true iff any of the following hold:
$$
\begin{array}{rcl}
\exists (k, \ell) \neq (i, j) &:& (i, j) \equiv (k, \ell) \\
\exists k &:& S[k] = (i, j) \\
\exists u &:& j \in \mathsf{CUS}_u \text{ and } p_u(\vec{w}_j) \text{ ``has support involving'' } w[i, j] \\
\exists v, s &:& j \in \mathsf{LOOK}_v \text{ and } q_{v,s}(\vec{w}_j) \text{ ``has support involving'' } w[i, j],
\end{array}
$$

Here $p_u, \ q_{v,s} \mathrel{⦂} \mathbb{F}^m \rightarrow \mathbb{F}$ are each [multivariate polynomials](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)) as defined in the relation description:

> Given $\eta$ symbols $X_0, \dots, X_{\eta-1}$ called indeterminates, a multivariate polynomial $P$ in these indeterminates, with coefficients in $\mathbb{F}$,
> is a finite linear combination $$P(X_0, \dots, X_{\eta-1}) = \sum_{z=0}^{\nu-1} \Big(c_z\, {\small\prod_{b=0}^{\eta-1}}\, X_b^{\alpha_{z,b}}\Big)$$ where $\nu \mathrel{⦂} \mathbb{N}$, $c_z \mathrel{⦂} \mathbb{F} \neq 0$, and $\alpha_{z,b} \mathrel{⦂} \mathbb{N}$.

$P(\vec{w}_j)$ "has support involving" its variable at index $i$, that is $w[i, j]$, iff $\exists z \in [0, \nu)$ s.t. $\alpha_{z,i} > 0$.

## Correctness-preserving translation of circuits

We define a correctness-preserving translation of circuits—this serves as the security notion that our optimizations must satisfy to ensure they do not introduce vulnerabilities.

For simplicity fix a field $\mathbb{F}$. What we mean by a correctness-preserving translation $\mathcal{T} \mathrel{⦂} \mathsf{AbstractCircuit}_{\mathbb{F}} \rightarrow \mathsf{ConcreteCircuit}_{\mathbb{F}}$ is that $\mathcal{T}$ is an efficiently computable function from abstract circuits to concrete circuits, such that for any abstract circuit $C$ with $C' = \mathcal{T}(C)$:
  * There is a bijective map $\mathcal{I}_C \mathrel{⦂} \mathbb{F}^{t} \rightarrow \mathbb{F}^{t'}$, efficiently computable in both directions, between abstract instances and concrete instances.
  * There is an efficient witness translation function $\mathcal{F}_C \mathrel{⦂} \mathbb{F}^{m \times n} \rightarrow \mathbb{F}^{m' \times n'}$ from abstract witnesses to concrete witnesses.
  * Completeness is preserved: given a satisfying instance $x$ and witness $w$ for the abstract circuit $C$, $w' = \mathcal{F}_C(w)$ is a satisfying witness for the concrete circuit $C'$ with instance $\mathcal{I}_C(x)$.
  * Knowledge soundness is preserved: given a satisfying instance $x'$ and witness $w'$ for the concrete circuit $C'$, we can efficiently compute some satisfying witness $w$ for the abstract circuit $C$ with instance $\mathcal{I}_C^{-1}(x')$.

We also claim that a correctness-preserving translation in this sense, when used with a concrete proof system that is zero-knowledge, necessarily yields an overall proof system for the abstract relation that is zero-knowledge. That is, informally, no additional information about the abstract witness is revealed beyond the fact that the prover knows such a witness.

> Aside: we could have required there to be an efficient reverse witness translation function $\mathcal{F}'_C \mathrel{⦂} \mathbb{F}_C^{m' \times n'} \rightarrow \mathbb{F}_C^{m \times n}$ from concrete witnesses to abstract witnesses, and then used $w = \mathcal{F}'_C(w')$ in the definition of knowledge soundness preservation. We do not take that approach because strictly speaking it would be an overspecification: we do not need the satisfying abstract witness to be *deterministically* and efficiently computable from the concrete witness; we only need it to be efficiently computable. Also, in general $w$ could also depend on the instance $x'$, not just $w'$. In practice, specifying such a function $\mathcal{F}'_C$ is likely to be the easiest way to prove knowledge soundness preservation.

## Efficiency improvements achieved by the abstract-to-concrete translations

These translations aim to improve circuit efficiency in the following ways:

1) Reduce the number of concrete columns.  Each set of offset columns can be represented using a single concrete witness column.  The number of witness columns impacts the size of the resulting zero-knowledge proof.
2) <span style="color:red">Mary:  Why do regions matter, and how do they improve efficiency? </span>
3) Reduce the overall circuit area:  When offset hints identify abstract cells as equivalent, the backend can optimize layout by reordering rows so that equivalent cells overlap in the concrete matrix, minimizing unused space.

## A model for a family of abstract-to-concrete translations and their correctness-preservation

```
+--------------------+  +-------------------+  +-------------------+
| translate_instance |  | translate_witness |  | translate_circuit |
+--------------------+  +-------------------+  +-------------------+
          ^                        ^                     ^
          |                        |                     |
          +------------------------+---------------------+
                                   |
                             +-----------+
                             | coord_map |
                             +-----------+
                                   ^
                                   |
                        +-----------------------+
                        |   compute_coord_map   |
                        | (uses designer hints) |
                        +-----------------------+
```

We propose a specific model for translating abstract circuits to concrete circuits, along with a correctness criterion that ensures such translations preserve the intended semantics. This model is not intended to capture all correctness-preserving translations, but rather to define one principled approach within that broader space.

To translate from abstract Plonkish to concrete Plonkish circuits, we introduce the following high-level functions:
* $\mathsf{translate\_circuit}$
* $\mathsf{translate\_instance}$
* $\mathsf{translate\_witness}$

Each of the functions $\mathsf{translate\_instance}$, $\mathsf{translate\_witness}$, and $\mathsf{translate\_circuit}$ depends on a coordinate mapping function, $\mathsf{coord\_map}$.

The function
$$
\mathsf{coord\_map} : [0, m) \times [0, n) \to [0, m') \times [0, n')
$$
is derived from design-time hints provided by the circuit author. To compute it, we define the function $\mathsf{compute\_coord\_map}$.  Here $m'$ and $n'$ are the number of concrete rows and columns respectively, with $m' \leq m$ and $n' \geq n$.

### Function $\mathsf{translate\_circuit}$ to translate the relation

The function
$$
\mathsf{translate\_circuit} : \mathsf{AbstractCircuit} \mapsto \mathsf{ConcreteCircuit}
$$
translates abstract Plonkish circuits to concrete Plonkish circuits.

The function
$$
\mathsf{translate\_circuit} : \mathsf{AbstractCircuit} \mapsto \mathsf{ConcreteCircuit}
$$
translates abstract Plonkish circuits to concrete Plonkish circuits.  Given $C \in \mathsf{AbstractCircuit}$ and hints $\mathsf{hints}$ it behaves as follows:

1) $(d', \mathsf{offsets}, m', n') := \mathsf{compute\_coord\_map}(C, \mathsf{hints} )$
2) $t' := t$
3) $\equiv$
4) $S$
5) $m_f'$
6) $f'$
7) $p_u'$ $
j' \in \mathsf{CUS}'_u \Rightarrow p_u\!\left(\big[\, w'[h_i, j' + e_i] : i \leftarrow 0 \text{..} m \,\big]\right) = 0
$
8) $\mathsf{CUS}_u' :=  \big\{\, \mathbf{r}(j) : j \in \mathsf{CUS}_u \,\big\}$
9)  $L_v'$
10) $\mathsf{TAB}_v'$
11) $q_{v,s}'$
12) $\mathsf{LOOK}_v'$


## Computing function $\mathsf{coord\_map}$ that gives the coordinate mapping

```
                             +-----------+
                             | coord_map |
                             +-----------+
                                   ^
                                   |
                        +-----------------------+
                        |   compute_coord_map   |
                        | (uses designer hints) |
                        +-----------------------+
                                   ^
                                   |
                        +--------------------+
                        |                    |
                   +--------+                |
                   | ok_for |                |
                   +--------+                |
                        ^                    |
                        |                    |
              +------------------------------+
              |                              |
    +-------------------+             +-------------+
    | working_coord_map |             | constrained |
    +-------------------+             +-------------+
```


The function
$$
\mathsf{compute\_coord\_map}
$$
takes as input an abstract circuit and a set of designer-provided hints $(C, \mathsf{hints}) \in \mathsf{AbstractCircuit} \times \mathsf{Hints}$.  The domain of abstract circuits, $\mathsf{AbstractCircuit}$, is defined formally in the description of the relation $\mathcal{R}_{\mathsf{plonkish}}$.  The domain of offset hints, $\mathsf{Hints}$, is defined in the following section.

It returns $(d', \mathsf{offsets}', m', n', \mathsf{coord\_map})$ such that :
- $d' \in \mathbb{N}$ is the number of offsets
- $\mathsf{offsets}' \in \mathbb{Z}^{d}$ are the offsets
- $m' \in \mathbb{N}$ is the number of concrete rows,
- $n' \in \mathbb{N}$ is the number of concrete columns,
- the coordinate mapping function
  $$
  \mathsf{coord\_map} : [0, m) \times [0, n) \to [0, m') \times [0, n')
  $$
   assigns concrete coordinates to each abstract cell position.

To translate the abstract circuit to a concrete circuit using the hints, we construct an injective mapping of abstract row numbers to concrete row numbers before applying offsets, such that:
* all *constrained* abstract cells map to concrete cell coordinates that are in range;
* every *constrained* abstract cell is represented by a distinct concrete cell, except that abstract cells that are equivalent under $\equiv$ *may* be identified.

### Hints

The domain $\mathsf{Hints}$ represents collections of designer-provided **offset hints**. Each hint assigns to a row index $i \in [0, m)$:

- a target row hint $h_i \in [0, m)$, and
- an offset expression $e_i \in \mathbb{Z}$.

We define:
$$
\mathsf{Hints} = \left( [0, m) \times \mathbb{Z} \right)^m
$$
that is, the set of length-$m$ sequences
$$
\mathsf{hints} : [0, m) \to [0, m) \times \mathbb{Z}
$$
where each entry $\mathsf{hints}[i]$ specifies a row hint and an offset for index $i$.

Thus $\mathsf{hints}[i] = (h_i, e_i)$  specifies:
- $h_i \in [0, m)$: a row hint, representing a target row index
- $e_i \in \mathbb{Z}$: an offset expression (e.g., a symbolic shift)

These hints guide the construction of the final coordinate map by specifying where (in rows) abstract elements prefer to appear and how to offset their placement in columns.

### Function $\mathsf{compute\_coord\_map}$ to compute the coordinate mapping

The function $\mathsf{compute\_coord\_map}$ computes the coordinate mapping $\mathsf{coord\_map}$ used as a subroutine in $\mathsf{translate\_instance}$, $\mathsf{translate\_witness}$, and $\mathsf{translate\_circuit}$.

It relies on two subroutines, whose input/output behavior is specified here. Their internal definitions will follow in subsequent sections.

- The function
  $$
  \mathsf{constrained} : \mathsf{AbstractCircuit} \times [0, m) \times [0, n) \to \{\mathsf{true}, \mathsf{false}\}
  $$
  returns whether a cell $(i, j)$ is constrained — for example, if it lies in a fixed column or participates in a copy, custom, or lookup constraint.

- The function
  $$
  \mathsf{ok\_for} : \mathsf{AbstractCircuit} \times \mathsf{Hints} \times \{ R \subseteq [0, n) \} \times ([0, n) \to [0, n'))  \to \{\mathsf{true}, \mathsf{false}\}
  $$
  returns whether the partial mapping $\mathbf{r}$ is valid for the set $R$ with respect to the given hints.

---

| $\mathsf{compute\_coord\_map}(C, \mathsf{hints}))$ |
|-------------------------------------|
| set $\mathsf{offsets} := \big\{\, e_i : (h_i, e_i) \in \mathsf{hints} \,\big\}$ |
| set $d':=$ size of $\mathsf{offsets}$ |
| set $m' := \max \big\{\, h_i : (h_i, e_i) \in \mathsf{hints} \,\big\}$ + 1 |
| set $\mathbf{r} := \{\}$ |
| set $a' := 0$ |
| for $g$ from $0$ to $n - 1$: |
| $\hspace{2em}$ find the minimal $g' \geq a'$ such that $\mathsf{ok\_for}(C, \mathsf{hints}, [0, g],\; \mathbf{r} \cup \{ g \mapsto g' \} ) = \mathsf{true}$ |
| $\hspace{2em}$ set $\mathbf{r} := \mathbf{r} \cup \{ g \mapsto g' \}$ and $a' := g' + 1$ |
| set $n' := \max \left\{\, \mathbf{r}(j) + e_i : (i, j) \in [0, m) \times [0, n),\; \mathsf{constrained}(C, i, j) \,\right\} + 1$ |
| set $\mathsf{coord\_map} \mathrel{\mathop:} [0, m) \times [0, n) \to [0, m') \times [0,n')$ such that $(i, j) \mapsto (h_i,\; \mathbf{r}(j) + e_i)$ |
| return ($d'$, $\mathsf{offsets}$, $m'$, $n'$, $\mathsf{coord\_map}$)|

---

The algorithm computes:
- The set $\mathsf{offsets}$ of unique offsets $e_i$ appearing in the hints.
- The size $d'$ of the $\mathsf{offsets}$
- The number of concrete rows $m'$ as one more than the maximum $h_i$ appearing in the hints.
- A strictly increasing function $\mathbf{r} : [0, n) \to [0, n')$ that maps abstract to concrete column indices.
- The number of concrete columns $n'$ as one more than the maximum $\mathbf{r}(j) + e_i$ across all constrained cells $(i, j)$.

The mapping $\mathsf{coord\_map}$ is then defined by:
$$
\mathsf{coord\_map}(i, j) = (h_i,\; \mathbf{r}(j) + e_i)
$$

A greedy strategy is used to construct $\mathbf{r}$ incrementally while maintaining strict monotonicity. At each step, the algorithm selects the smallest $g' \geq a'$ such that extending $\mathbf{r}$ with $g \mapsto g'$ preserves the validity of all previous assignments, as checked by $\mathsf{ok\_for}$.

**Correctness guarantee.**
The algorithm always succeeds in finding such a $g'$ at each step. Since there is no upper bound on $g'$, we can always find one large enough to avoid conflicts. Specifically, when assigning $\mathbf{r}(g) = g'$, it suffices to ensure that:
$$
(h_i,\; g' + e_i) \neq (h_k,\; \mathbf{r}(\ell) + e_k)
$$
for all $\ell < g$ and all $i, k \in [0, m)$ such that both $(i, g)$ and $(k, \ell)$ are constrained. This ensures non-overlapping coordinate assignments for constrained cells.


### Function $\mathsf{constrained}$ to check if cells are constrained

We now define the function
$$
\mathsf{constrained} : \mathsf{AbstractCircuit} \times [0, m) \times [0, n) \to \{ \mathsf{true}, \mathsf{false} \}
$$
which was used in the $\mathsf{compute\_coord\_map}$ algorithm to determine whether a given abstract cell $(i, j)$ must be assigned a coordinate in the final layout.

This function returns $\mathsf{true}$ if and only if the cell $w[i, j]$ is involved in any fixed value, equality, custom constraint, or lookup constraint.

---

In the abstract circuit $C \in \mathsf{AbstractCircuit}$, let each custom constraint polynomial $p_u : \mathbb{F}^m \to \mathbb{F}$ be written as
$$
p_u(\vec{w}_j) = \sum_{z=0}^{\nu - 1} \sum_{i=0}^{m - 1} \alpha_{u,z,i} \cdot m_{z,i}(\vec{w}_j),
$$
and similarly, each lookup constraint polynomial $q_{v,s} : \mathbb{F}^m \to \mathbb{F}$ is written as
$$
q_{v,s}(\vec{w}_j) = \sum_{z=0}^{\nu - 1} \sum_{i=0}^{m - 1} \beta_{v, s,z,i} \cdot n_{z,i}(\vec{w}_j),
$$
where $m_{z,i}$ and $n_{z,i}$ are monomials in the vector $\vec{w}_j$, and $\alpha_{u,z,i}, \beta_{v,s,z,i} \in \mathbb{F}$ are the corresponding coefficients.

___

| $\mathsf{constrained}(C, i, j )$ |
|-------------------------------------|
| check if $i < m_f$ |
| check if $\exists (k, \ell) \neq (i, j) : (i, j) \equiv (k, \ell)$ |
| check if $\exists k : S[k] = (i, j)$ |
| check if $\exists u : j \in \mathsf{CUS}_u$ and $\exists z \in [0, \nu)$  such that $\alpha_{u,z,i} > 0$ |
| check if $\exists v, s : j \in \mathsf{LOOK}_v$ and $\exists z \in [0, \nu)$ such that $\beta_{v,s,z,i} > 0$ |
| if any check passes then return $\mathsf{true}$  |
| else return $\mathsf{false}$|

In other words, a cell $w[i, j]$ is considered constrained if it either contains a fixed value, participates in equality or permutation constraints, or contributes (with nonzero coefficient) to a custom or lookup constraint polynomial applied to column $j$.



### Function $\mathsf{ok\_for}$ to check if current offsets are OK.

We now define the function
$$
\mathsf{ok\_for} : \mathsf{AbstractCircuit} \times \mathsf{Hints} \times \{ R \subseteq [0, n) \} \times ([0, n) \to [0, n'))  \to \{\mathsf{true}, \mathsf{false}\}
$$
that returns whether the partial mapping $\mathbf{r}$ is valid for the set $R$ with respect to the given hints.

It relies on the subroutine
  $$
  \mathsf{working\_coord\_map} : \mathsf{Hints} \times ([0, n) \to [0, n')) \times [0, m) \times [0, n) \to \mathbb{N} \times \mathbb{N}
  $$
that takes as input a set of hints, an offset function $\mathbf{r}, and coordinates $(i,j)$ and behaves as follows

| $\mathsf{working\_coord\_map}(\mathsf{hints}, \mathbf{r}, i, j )$ |
|-------------------------------------|
| set $(h_i, e_i) := \mathsf{hints}[i]$ |
| set $i' := h_i$ |
| set $j' := \mathbf{r}(j) + e_i$ |
| return $(i', j')$|



We now specify $\mathsf{ok\_for}$ that checks that constrained cells have unique coordinates in the concrete circuit.

| $\mathsf{ok\_for}(C, \mathsf{hints}, R,  \mathbf{r},  )$ |
|-------------------------------------|
| set $m' := \max \big\{\, h_i : (h_i, e_i) \in \mathsf{hints} \,\big\} + 1$|
| set $m:=$ the number of hints|
| for $(i,j) \in [0,m) \times R$ and for $(k, \ell) \in [0,m) \times R$: |
| $\hspace{2em}$ if $\mathsf{constrained}(C, i, j):$ |
| $\hspace{4em}$ check $\mathsf{working\_coord\_map}(\mathsf{hints}, \mathbf{r}, i, j) \in [0,m') \times \mathbb{N}$|
| $\hspace{4em}$ if $\mathsf{constrained}(C, k, \ell)$ and $(i,j) \neq (k, \ell):$|
| $\hspace{6em}$ check $\mathsf{working\_coord\_map}(\mathsf{hints}, \mathbf{r}, i, j) \neq \mathsf{working\_coord\_map}(\mathsf{hints}, \mathbf{r}, k, \ell)$|
| return $\mathsf{true}$ if all checks pass|
| else return $\mathsf{false}$|

We adopt the convention that indexing outside $w'$ results in an undefined value (i.e. the adversary could choose it).  Tesselation between custom constraints is represented by equivalence under $\equiv$.

Discussion: It is alright if one or more *unconstrained* abstract cells map to the same concrete cell as a constrained abstract cell, because that will not affect the meaning of the circuit. Notice that specifying $\equiv$ as an equivalence relation helps to simplify this definition (as compared to specifying it as a set of copy constraints), because an equivalence relation is by definition symmetric, reflexive, and transitive.



## Translating the circuits

We adopt the convention that indexing outside $w'$ results in an undefined value (i.e. the adversary could choose it).  Tesselation between custom constraints is represented by equivalence under $\equiv$.

A translation from an abstract to a concrete circuit takes the following inputs:

| Translation input  | Description |
| ------------------ | -------- |
| input circuit      | The abstract circuit, excluding the instance vector $\phi$. |
| offset hints       | $\big[\, (h_i, e_i) \mathrel{⦂} [0,m') \times \mathbb{Z} \,:\, i \leftarrow 0 \text{..} m \,\big]$ provided by the circuit designer. |

And produces:

| Translation output | Description |
| ------------------ | -------- |
| output circuit     | A version of the input circuit that supports assigning polynomials to cells on offset rows. |


In our model:

* The abstract witness matrix $w$ has $m$ abstract columns.
* The concrete witness matrix $w'$ has $m'$ columns, of which the first $m'_f$ are fixed.


### Witness translations

The constrained abstract cells $w \mathrel{⦂} \mathbb{F}^{m \times n}$ are translated to concrete cells $w' \mathrel{⦂} \mathbb{F}^{m' \times n'}$:
$$
\mathsf{constrained}(i, j) \Rightarrow w'[\mathsf{coord\_map}[i, j]] = w[i, j]
$$

The values of concrete cells not corresponding to any constrained abstract cell are arbitrary.

The fixed abstract cells $f \mathrel{⦂} \mathbb{F}^{m_f \times n}$ are similarly translated to fixed concrete cells $f' \mathrel{⦂} \mathbb{F}^{m'_f \times n'}$:
$$
f'[\mathsf{coord\_map}[i, j]] = f[i, j]
$$

Fixed concrete cells not assigned values by this translation are filled with zeros.

The abstract coordinates appearing in $\equiv$ and $S$ are similarly mapped to their concrete coordinates.

### Constraint translations

The conditions for custom constraints in the concrete circuit are then given by:
$$
\mathsf{CUS}'_u = \big\{\, \mathbf{r}(j) : j \in \mathsf{CUS}_u \,\big\} \\[0.6ex]
j' \in \mathsf{CUS}'_u \Rightarrow p_u\!\left(\big[\, w'[h_i, j' + e_i] : i \leftarrow 0 \text{..} m \,\big]\right) = 0
$$

and similarly for lookups:
$$
\mathsf{LOOK}'_v = \big\{\, \mathbf{r}(j) : j \in \mathsf{LOOK}_v \,\big\} \\[0.6ex]
j' \in \mathsf{LOOK}'_v \Rightarrow \big[\, q_{v,s}\!\left(\big[\,w'[h_i, j' + e_i] : i \leftarrow 0 \text{..} m \,\big]\right) : s \leftarrow 0 \text{..} L_v \,\big] \in \mathsf{TAB}_v
$$



### Security proofs


Recall from the [relation definition](relation.md#copy-constraints) that fixed abstract cells with the same value are considered to be equivalent under $\equiv$. This allows a fixed column to be specified as a rotation of another fixed column, which can be useful to reduce the number of fixed concrete columns used by the concrete circuit.

Since correctness does not depend on the specific hints provided by the circuit programmer, it is also valid to use any subset of the provided hints, or to infer hints that were not provided.


* **Fixed-column consistency**: $i < m_f \Rightarrow h_i < m'_f$, i.e. the concrete circuit follows the same rule as the abstract circuit that fixed columns are on the left.
* **Semantics preservation**:  The hints do not affect the meaning of a circuit, i.e., the set of public inputs for which it is satisfiable, and the knowledge required to find a witness.
  <span style="color:red">Mary:  This is not concrete??? </span>



#### $\mathsf{FIND\_ROW\_MAPPING}$ gives a correctness-preserving translation

Recall from [Correctness-preserving translation of circuits](#correctness-preserving-translation-of-circuits) above that:

> What we mean by a correctness-preserving translation is that we know an efficient translation function from abstract circuits to concrete circuits, such that for any given translation:
>   * There is a bijective map $\mathcal{I} \mathrel{⦂} \mathbb{F}^t \rightarrow \mathbb{F}^{t'}$, efficiently computable in both directions, between abstract instances and concrete instances.
>   * There is an efficient witness translation function $\mathcal{F} \mathrel{⦂} \mathbb{F}^{m \times n} \rightarrow \mathbb{F}^{m' \times n'}$ from abstract witnesses to concrete witnesses.
>   * Completeness is preserved: given a satisfying instance $x$ and witness $w$ for the abstract circuit, $w' = \mathcal{F}(w)$ is a satisfying witness for the concrete circuit with instance $\mathcal{I}(x)$.
>   * Knowledge soundness is preserved: given a satisfying instance $x'$ and witness $w'$ for the concrete circuit, we can efficiently compute some satisfying witness $w$ for the abstract circuit with instance $\mathcal{I}^{-1}(x')$.

Define $\mathcal{I}(x) = x$, which is clearly invertible and efficiently computable in both directions.

The concrete witness $w' \mathrel{⦂} \mathbb{F}^{m' \times n'}$ consists of the matrix of concrete values provided by the prover, as defined in [Preliminary definitions](#preliminary-definitions). Like the abstract witness, it consists of the (potentially private) prover inputs to the concrete circuit, and any intermediate values (including fixed values) that are not inputs to the concrete circuit but are required in order to satisfy it.

We now define our efficient abstract-to-concrete witness translation function $\mathcal{F}$, which maps from the abstract witness $w$ to the concrete witness $w'$, by giving its value $\mathcal{F}(w) = w'$ for every cell.

Let $n'$ and $m'$ be as defined by $\mathsf{FIND\_ROW\_MAPPING}$ above. Let $\mathsf{coord\_map}$ be as defined in (1).

Let $\mathsf{inv\_coord\_map} \mathrel{⦂} (m' \times n') \rightarrow (m \times n) \cup \{\bot\}$ be defined such that $\mathsf{inv\_coord\_map}[i', j']$ is the unique $(i, j) \in [0, m) \times [0, n)$ such that $\mathsf{constrained}[i, j]$ is true and $\mathsf{coord\_map}[i, j] = (i', j')$, or $\bot$ if there is no such $(i, j)$.

Then let $\mathcal{F}(w) = w'$ where
$$
w'[i', j'] = \begin{cases}
  w[\mathsf{inv\_coord\_map}[i', j']], &\text{if } \mathsf{inv\_coord\_map}[i', j'] \neq \bot \\
  0,                                   &\text{otherwise.}
\end{cases}
$$

This completely specifies $\mathcal{F}$, and furthermore shows that $\mathcal{F}$ is efficiently computable.

Note that $\mathsf{inv\_coord\_map}$ is well-defined because $\mathsf{FIND\_ROW\_MAPPING}$ ensures by construction that $\mathsf{ok\_for}([0, n), \mathbf{r}, \mathsf{hints})$ holds, where
$$
\begin{array}{rcl}
\mathsf{ok\_for}(R, \mathbf{r}, \mathsf{hints}) &=& \forall (i, j), (k, \ell) \in ([0, m) \times R) \times ([0, m) \times R) :\\[0.5ex]
&& \hspace{2em} (\mathsf{constrained}[i, j] \;\Rightarrow\; \mathsf{coord\_map}[i, j] \in [0, m') \times \mathbb{N} \;\;\wedge\; \\[0.3ex]
&& \hspace{2em} (\mathsf{constrained}[i, j] \;\wedge\; \mathsf{constrained}[k, \ell] \;\wedge\; (i, j) \not\equiv (k, \ell) \;\Rightarrow\; \mathsf{coord\_map}[i, j] \neq \mathsf{coord\_map}[k, \ell]) \\
\end{array}
$$

We can also define an efficient concrete-to-abstract witness translation function $\mathcal{F}' \mathrel{⦂} \mathbb{F}^{m' \times n'} \rightarrow \mathbb{F}^{m \times n}$, by similarly giving its value for every cell:

Let $\mathcal{F}'(w') = w$ where $w[i, j] = w'[\mathsf{coord\_map}[i, j]]$.

(It happens that $\mathcal{F}'$ as we have defined it here is a [left inverse](https://en.wikipedia.org/wiki/Inverse_function#Left_inverses) of $\mathcal{F}$. This is not strictly necessary since the values of unconstrained abstract cells could be arbitrary.)

In order that $\mathsf{FIND\_ROW\_MAPPING}$ gives a correctness-preserving translation, it remains to show that:
1. Completeness is preserved: $\forall (x, w) \in \mathcal{R}_{\mathsf{plonkish}}$, $(x', w') = (\mathcal{I}(x), \mathcal{F}(w)) = (x, \mathcal{F}(w)) \in \mathcal{R}_{\mathsf{concrete}}$.
2. Knowledge soundness is preserved: $\forall (x', w') \in \mathcal{R}_{\mathsf{concrete}}$, we can efficiently compute $w = \mathcal{F}'(w')$ such that $(\mathcal{I}^{-1}(x'), w) = (x', w) \in \mathcal{R}_{\mathsf{plonkish}}$.

For condition 1, we have $\forall (x, w) \in \mathcal{R}_{\mathsf{plonkish}}$, which means that
$$
\begin{array}{ll|l}
   w \mathrel{⦂} \mathbb{F}^{m \times n}, \ f \mathrel{⦂} \mathbb{F}^{m_f \times n} & & i \in [0,m_f), \ j \in [0,n) \Rightarrow w[i, j] = f[i, j] \\[0.3ex]
   S \mathrel{⦂} ([0,m) \times [0,n))^t, \ \phi \mathrel{⦂} \mathbb{F}^t & & k \in [0,t) \Rightarrow w[S[k]] = \phi[k] \\[0.3ex]
   \equiv\; \subseteq ([0,m) \times [0,n)) \times ([0,m) \times [0,n)) & & (i,j) \equiv (k,\ell) \Rightarrow w[i, j] = w[k, \ell] \\[0.3ex]
   \mathsf{CUS}_u \subseteq [0,n), \ p_u \mathrel{⦂} \mathbb{F}^m \rightarrow \mathbb{F} & & j \in \mathsf{CUS}_u \Rightarrow p_u(\vec{w}_j) = 0 \\[0.3ex]
   \mathsf{LOOK}_v \subseteq [0,n), \ q_{v,s} \mathrel{⦂} \mathbb{F}^m \rightarrow \mathbb{F}, \ \mathsf{TAB}_v \subseteq \mathbb{F}^{L_v} & & j \in \mathsf{LOOK}_v \Rightarrow \big[\, q_{v,s}(\vec{w}_j) : s \leftarrow 0 \text{..} L_v \,\big] \in \mathsf{TAB}_v
\end{array}
$$

We must prove that this implies $(x, \mathcal{F}(w)) \in \mathcal{R}_{\mathsf{concrete}}$, i.e.
$$
\begin{array}{ll|l}
   w' \mathrel{⦂} \mathbb{F}^{m' \times n'}, \ f' \mathrel{⦂} \mathbb{F}^{m'_f \times n'} & & i' \in [0,m'_f), \ j' \in [0,n') \Rightarrow w'[i', j'] = f[i', j'] \\[0.3ex]
   S' \mathrel{⦂} ([0,m') \times [0,n'))^t, \ \phi \mathrel{⦂} \mathbb{F}^t & & k \in [0,t) \Rightarrow w'[S'[k]] = \phi[k] \\[0.3ex]
   \equiv'\; \subseteq ([0,m') \times [0,n')) \times ([0,m') \times [0,n')) & & (i',j') \equiv (k',\ell') \Rightarrow w'[i', j'] = w'[k', \ell'] \\[0.3ex]
   \mathsf{CUS}'_u \subseteq [0,n'), \ p'_u \mathrel{⦂} \mathbb{F}^{m'} \rightarrow \mathbb{F} & & j' \in \mathsf{CUS}'_u \Rightarrow p'_u(\vec{w}'_{j'}) = 0 \\[0.3ex]
   \mathsf{LOOK}'_v \subseteq [0,n'), \ q'_{v,s} \mathrel{⦂} \mathbb{F}^{m'} \rightarrow \mathbb{F}, \ \mathsf{TAB}_v \subseteq \mathbb{F}^{L_v} & & j' \in \mathsf{LOOK}'_v \Rightarrow \big[\, q'_{v,s}(\vec{w}'_{j'}) : s \leftarrow 0 \text{..} L_v \,\big] \in \mathsf{TAB}_v
\end{array}
$$

For condition 2, the abstract witness $w$ that we find will be $\mathcal{F}'(x')$. Since $\mathcal{I}$ is the identity function, we have that for any $(x', w') \mathrel{⦂} \mathbb{F}^t \times \mathbb{F}^{m' \times n'}$, $(\mathcal{I}^{-1}(x'), \mathcal{F}'(x')) = (x', w)$ exists and is efficiently computable. We must also prove that $(x', w') \in \mathcal{R}_{\mathsf{concrete}} \Rightarrow (x', w) \in \mathcal{R}_{\mathsf{plonkish}}$ (i.e. loosely speaking, the converse of what we need to prove for condition 1).

Given the definitions from [above](#constraint-translations), it is straightforward to see [FIXME] that in the statements to be proven for both conditions:

* the concrete fixed constraints for concrete fixed cells $(i',j')$ are in one-to-one correspondence with equivalent abstract fixed constraints for abstract cells $(i,j)$;
* the concrete input constraints for concrete cells $S'[k]$, $k \in [0,t)$ are in one-to-one correspondence with equivalent abstract input constraints for abstract cells $S[k]$, $k \in [0,t)$;
* the concrete equality constraints for concrete cells $(i',j') \equiv' (k',\ell')$ are in one-to-one correspondence with equivalent abstract equality constraints for abstract cells $(i,j) \equiv (k,\ell)$;
* the concrete custom constraints for concrete rows $j' \in \mathsf{CUS}'_u$, are in one-to-one correspondence with equivalent abstract custom constraints for abstract rows $j \in \mathsf{CUS}_u$;
* the concrete lookup constraints for concrete rows $j' \in \mathsf{LOOK}'_v$, are in one-to-one correspondence with equivalent abstract lookup constraints for abstract rows $j \in \mathsf{LOOK}_v$.

By "equivalent" here we mean that each concrete constraint is satisfied if and only if the corresponding abstract constraint is satisfied, given the above mappings between $(x, w)$ and $(x', w')$. Since the concrete and abstract constraints are also in one-to-one correspondence, all of the concrete constraints are satisfied if and only if all of the abstract constraints are satisfied.

The "if" direction implies condition 1, and the "only if" direction implies condition 2. Therefore, both completeness and knowledge soundness are preserved. $\blacksquare$
