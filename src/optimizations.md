# Plonkish Backend Optimizations

## Background

The relation described in [Specification of the Plonkish Relation](relation.md) gives an abstract model of a Plonkish constraint system that is sufficiently expressive, but does not take into account some of the optimizations that are commonly used in Plonkish implementations, such as the use of offsets/rotations in Plonkish custom constraints.

The benefit of the simpler abstract model is that it allows reasoning about the circuit without needing to be concerned with layout of the witness matrix, i.e. the position of rows relative to each other. The drawback of using only the abstract model, is that it may require a greater number of columns to express a given circuit than a model that supports offsets. This directly affects proof size for popular instantiations of proof systems based on Plonkish.

In this document we specify a method to translate from an abstract circuit to a concrete one, that retains the zero-knowledge, (knowledge) soundness, and completeness of the abstract system. This can include automated optimizations, which are able to reorder the rows as needed without changing the meaning of the circuit.

The optimizations suggested in this specification would be impractical or error-prone to do manually, because they rely on global optimization of the witness matrix layout. [TODO: make this more convincing or give examples.]

## Preliminary definitions

If not otherwise defined, variable names used here are consistent with [the relation description](relation.md).

We will use the convention that variables marked with a prime ($'$) refer to *concrete* column or row indices.

An "abstract cell" specifies an entry in the witness matrix $w$ of the abstract circuit. A "concrete cell" specifies an entry in the witness matrix $w'$ of the concrete circuit.

We will denote the witness value at column $i$ and row $j$ as $w[i, j]$.

We say that an abstract cell with coordinates $(i, j)$ is "constrained" if it is in a fixed column or if it appears in some copy, custom, or lookup constraint. More precisely, $\mathsf{constrained}[i, j]$ is true iff any of the following hold:
$$
\begin{array}{rcl}
&& i < m_f \\
\exists (k, \ell) \neq (i, j) &:& (i, j) \equiv (k, \ell) \\
\exists k &:& ((i, j), k) \in S \\
\exists u &:& j \in \mathsf{CUS}_u \text{ and } w[i, j] \text{ ``might be used'' in } p_u(\vec{w}_j) \\
\exists v, s &:& j \in \mathsf{LOOK}_v \text{ and } w[i, j] \text{ ``might be used'' in } q_{v,s}(\vec{w}_j),
\end{array}
$$

Here $p_u, \ q_{v,s} \mathrel{⦂} \mathbb{F}^m \rightarrow \mathbb{F}$ are each [multivariate polynomials](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)) as defined in the relation description:

> Given $\eta$ symbols $X_0, \dots, X_{\eta-1}$ called indeterminates, a multivariate polynomial $P$ in these indeterminates, with coefficients in $\mathbb{F}$,
> is a finite linear combination $$P(X_0, \dots, X_{\eta-1}) = \sum_{z=0}^{\nu-1} \Big(c_z\, {\small\prod_{b=0}^{\eta-1}}\, X_b^{\alpha_{z,b}}\Big)$$ where $\nu \mathrel{⦂} \mathbb{N}$, $c_z \mathrel{⦂} \mathbb{F} \neq 0$, and $\alpha_{z,b} \mathrel{⦂} \mathbb{N}$.

Cell $w[i, j]$ "might be used" in $P(\vec{w}_j)$ iff $\exists z \in [0, \nu)$ s.t. $\alpha_{z,i} > 0$.

## Correctness-preserving translation of circuits

What we mean by a correctness-preserving translation is that we know an efficient translation function from abstract circuits to concrete circuits, such that for any given translation:
  * There is a bijective map $\mathcal{I}$, efficiently computable in both directions, between abstract instances and concrete instances.
  * There is an efficient witness translation function $\mathcal{F}$ from abstract witnesses to concrete witnesses.
  * Completeness is preserved: given a satisfying instance $x$ and witness $w$ for the abstract circuit, $w' = \mathcal{F}(w)$ is a satisfying witness for the concrete circuit with instance $\mathcal{I}(x)$.
  * Knowledge soundness is preserved: given a satisfying instance $x'$ and witness $w'$ for the concrete circuit, we can efficiently compute some satisfying witness $w$ for the abstract circuit with instance $\mathcal{I}^{-1}(x')$.

We also claim that a correctness-preserving translation in this sense, when used with a concrete proof system that is zero-knowledge, necessarily yields an overall proof system for the abstract relation that is zero-knowledge. That is, informally, no additional information about the abstract witness is revealed beyond the fact that the prover knows such a witness.

## A model for a class of abstract-to-concrete translations and their correctness

We give a specific model for a family of translations, and a criterion for them to be correctness-preserving consistent with the above definition. Note that this is very far from covering all possible correctness-preserving translations.

In our model, the abstract witness matrix $w$ consists of $m$ abstract columns, and the concrete witness matrix $w'$ consists of $m'$ concrete columns, of which the first $m'_f$ are fixed. A translation from an abstract to a concrete circuit will take inputs of the following form:

| Translation input  | Description |
| ------------------ | -------- |
| input circuit      | This is the instance excluding the instance vector $\phi$. |
| offset hints       | $\big[\, (h_i, e_i) \mathrel{⦂} [0,m') \times \mathbb{Z} \,:\, i \leftarrow 0 \text{..} m \,\big]$ provided by the circuit designer. |

| Translation output | Description |
| ------------------ | -------- |
| output circuit     | This is like the input circuit but also supports applying the polynomials to cells on offset rows. |

### Adapting $\mathcal{R}_{\mathsf{plonkish}}$ to concrete circuits

To define a relation for concrete circuits, it is necessary to directly handle row offsets.

Let $\mathsf{offsets}$ be the sequence of row offsets that are available to be used in concrete gates and concrete lookups.

Informally, we define $\mathcal{R}_{\mathsf{concrete}}$ to be $\mathcal{R}_{\mathsf{plonkish}}$ with the following changes:

* $\vec{w'}_{j'}$ is defined as the row vector $\big[\, w'[i, j' + \mathsf{offset}] : (i', \mathsf{offset}) \leftarrow (0 \text{..} n') \times \mathsf{offsets} \,\big]$.
* $p_u$ and $q_{v,s}$ are each of type $\mathbb{F}^{\,\mathsf{windowsize}} \rightarrow \mathbb{F}$ where $\mathsf{windowsize} = m' \,\cdot\; \#\mathsf{offsets}$, instead of $\mathbb{F}^m \rightarrow \mathbb{F}$. They are applied to $\vec{w'}_{j'}$ as just defined instead of $\vec{w}_j$.

We adopt the convention that indexing outside $w'$ results in an undefined value (i.e. the adversary could choose it).

### Hints

Offsets are represented by hints $\big[\, (h_i, e_i) \,\big]$. To simplify the programming model, the hints are not supposed to affect the meaning of a circuit (i.e. the set of public inputs for which it is satisfiable, and the knowledge required to find a witness).

For simplicity we require that $i < m_f \Rightarrow h_i < m'_f$, i.e. the concrete circuit follows the same rule as the abstract circuit that fixed columns are on the left.

Tesselation between custom constraints is just represented by equivalence under $\equiv$. When the offset hints indicate that two concrete cells in the same column are equivalent, the backend can optimize overall circuit area by reordering the rows so that the equivalent cells overlap.

More specifically, to translate the abstract circuit to a concrete circuit using the hints $\big[\, (h_i, e_i) \,\big]_i$, we construct an injective mapping of abstract row numbers to concrete row numbers before applying offsets, $\mathbf{r} \mathrel{⦂} [0, n) \rightarrow [0, n')$ with $n' \geq n$, such that the abstract cell with coordinates $(i, j)$ maps to the concrete cell with coordinates $(h_i, \mathbf{r}(j) + e_i)$, where:
* all *constrained* abstract cells map to concrete cell coordinates that are in range;
* every *constrained* abstract cell is represented by a distinct concrete cell, except that abstract cells that are equivalent under $\equiv$ *may* be identified.

For given hints $\mathsf{hints} = \big[\, (h_i, e_i) \mathrel{⦂} [0, m') \times \mathbb{Z} \,:\, i \leftarrow 0 \text{..} m \,\big]$, define the coordinate mapping $\mathsf{coord\_map} \mathrel{⦂} [0, m) \times [0, n) \rightarrow [0, m') \times \mathbb{Z}$ as
$$
\mathsf{coord\_map}[i, j] = (h_i, \mathbf{r}(j) + e_i) \tag{1}
$$

Then, for $R \subseteq [0, n)$ and $\mathsf{hints}$ as above, define
$$
\begin{array}{rcl}
\mathsf{ok\_for}(R, \mathbf{r}, \mathsf{hints}) &=& \forall (i, j), (k, \ell) \in ([0, m) \times R) \times ([0, m) \times R) :\\[0.5ex]
&& \hspace{2em} (\mathsf{constrained}[i, j] \;\Rightarrow\; \mathsf{coord\_map}[i, j] \in [0, m') \times \mathbb{N} \;\;\wedge\; \\[0.3ex]
&& \hspace{2em} (\mathsf{constrained}[i, j] \;\wedge\; \mathsf{constrained}[k, \ell] \;\wedge\; (i, j) \not\equiv (k, \ell) \;\Rightarrow\; \mathsf{coord\_map}[i, j] \neq \mathsf{coord\_map}[k, \ell]) \\
\end{array}
$$

Then, the overall correctness condition is that $\mathbf{r}$ must be chosen such that $\mathsf{ok\_for}([0, n), \mathbf{r}, \mathsf{hints})$. We claim that this implies the more general definition of correctness preservation for this family of translations.

> Proof sketch [TODO remove handwaving]:
>
> $\mathcal{I}$ is the identity function and $\mathcal{F}$ is described below. $\mathcal{F}$, $\mathcal{I}$, and $\mathcal{I}^{-1}$ are obviously efficiently computable. Given that the concrete custom constraints and lookups are just the abstract constraints and lookups modified to access the same witness values in their translated locations (and the translation mapping is bijective), preservation of completeness follows immediately. Preservation of knowledge soundness holds because, informally, we can invert the coordinate translation defined by $\mathcal{F}$ to reconstruct all of the abstract witness cells that are needed to satisfy the abstract relation.

Discussion: It is alright if one or more *unconstrained* abstract cells map to the same concrete cell as a constrained abstract cell, because that will not affect the meaning of the circuit. Notice that specifying $\equiv$ as an equivalence relation helps to simplify this definition (as compared to specifying it as a set of copy constraints), because an equivalence relation is by definition symmetric, reflexive, and transitive.

Recall from the [relation definition](relation.md#copy-constraints) that fixed abstract cells with the same value are considered to be equivalent under $\equiv$. This allows a fixed column to be specified as a rotation of another fixed column, which can be useful to reduce the number of fixed concrete columns used by the concrete circuit.

Since correctness does not depend on the specific hints provided by the circuit programmer, it is also valid to use any subset of the provided hints, or to infer hints that were not provided.

### Witness translations

The constrained abstract cells $w \mathrel{⦂} \mathbb{F}^{m \times n}$ are translated to concrete cells $w' \mathrel{⦂} \mathbb{F}^{m' \times n'}$:
$$
\mathsf{constrained}(i, j) \Rightarrow w'[\mathsf{coord\_map}((i, j))] = w[i, j]
$$

The values of concrete cells not corresponding to any constrained abstract cell are arbitrary.

The fixed abstract cells $f \mathrel{⦂} \mathbb{F}^{m_f \times n}$ are similarly translated to fixed concrete cells $f' \mathrel{⦂} \mathbb{F}^{m'_f \times n'}$:
$$
f'[\mathsf{coord\_map}((i, j))] = f[i, j]
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

### Algorithm $\mathsf{FIND\_ROW\_MAPPING}$: Greedy algorithm for choosing $\mathbf{r}$

There is a greedy algorithm for deterministically choosing $\mathbf{r}$ that maintains ordering of rows (i.e. $\mathbf{r}$ is strictly increasing), and simply inserts a gap in the row mapping whenever the above constraint would not be met for all rows so far.

| Algorithm for choosing $\mathbf{r}$ |
|----|
| set $\mathbf{r} := \{\}$ |
| set $a' := 0$ |
| for $g$ from $0$ up to $n-1$: |
| $\hspace{2em}$ find the minimal $g' \geq a'$ such that $\mathsf{ok\_for}([0, g], \mathbf{r} \cup \{g \mapsto g'\}, \mathsf{hints})$ |
| $\hspace{2em}$ set $\mathbf{r} := \mathbf{r} \cup \{g \mapsto g'\}$ and $a' := g'+1$ |

The number of concrete rows is then given by $n' = \max \big\{\, \mathbf{r}(j) + e_i : (i, j) \in ([0, m) \times [0, n)) \;\wedge\; \mathsf{constrained}(i, j) \,\big\} + 1$.

### Security proofs

#### $\mathsf{FIND\_ROW\_MAPPING}$ gives a correctness-preserving translation

Let $\mathsf{coord\_map}$ be as defined in (1).

We can define $\mathcal{F}$ by giving its value $\mathcal{F}(w) = w'$ for every cell in $w'$.

Because we have $\mathsf{ok\_for}([0, n), \mathbf{r}, \mathsf{hints})$ where
$$
\begin{array}{rcl}
\mathsf{ok\_for}(R, \mathbf{r}, \mathsf{hints}) &=& \forall (i, j), (k, \ell) \in ([0, m) \times R) \times ([0, m) \times R) :\\[0.5ex]
&& \hspace{2em} (\mathsf{constrained}[i, j] \;\Rightarrow\; \mathsf{coord\_map}[i, j] \in [0, m') \times \mathbb{N} \;\;\wedge\; \\[0.3ex]
&& \hspace{2em} (\mathsf{constrained}[i, j] \;\wedge\; \mathsf{constrained}[k, \ell] \;\wedge\; (i, j) \not\equiv (k, \ell) \;\Rightarrow\; \mathsf{coord\_map}[i, j] \neq \mathsf{coord\_map}[k, \ell]) \\
\end{array}
$$
it must be the case that for any $(i', j') \in [0, m') \times [0, n')$, there is at most one $(i, j) \in [0, m) \times [0, n)$ such that $\mathsf{constrained}[i, j]$ and $\mathsf{coord_map}[i, j] = (i', j')$. If there is no such $(i, j)$ then set $w'[i', j'] = 0$, otherwise set $w'[i', j'] = w[i, j]$.

This completely specifies $\mathcal{F}$, and furthermore shows that $\mathcal{F}$ is efficiently computable.

Define $\mathcal{I}(x) = x$, which is obviously invertible.

In order that $\mathsf{FIND\_ROW\_MAPPING}$ gives a correctness-preserving translation, it remains to show:
1. $\forall (x, w) \in \mathcal{R}_{\mathsf{plonkish}}$, $(x', w') = (\mathcal{I}(x), \mathcal{F}(w)) = (x, \mathcal{F}(w)) \in \mathcal{R}_{\mathsf{concrete}}$.
2. $\forall (x', w') \in \mathcal{R}_{\mathsf{concrete}}$, we can efficiently compute some $w$ such that $(\mathcal{I}^{-1}(x'), w) = (x', w) \in \mathcal{R}_{\mathsf{plonkish}}$.

TODO: fill in the gaps.

Condition 1 is met because for each step it is always possible to find a suitable $g'$: there is no upper bound on $g'$, and so we can always choose it large enough that any additional conditions of $\mathsf{ok\_for}([0, g], \mathbf{r} \cup \{g \mapsto g'\}, \mathsf{hints})$ relative to $\mathsf{ok\_for}([0, g-1], \mathbf{r}, \mathsf{hints})$ hold. Specifically: by symmetry it is sufficient to consider the additional conditions for which $j = g$ and $\ell < g$. There must be some $g' = \mathbf{r}(j)$ such that $(h_i, g' + e_i)$ does not overlap with $(h_k, \mathbf{r}(\ell) + e_k)$ for any $i, k \in [0, m)$ and $\ell \in [0, g-1]$.

Condition 2 is met because in the last step the algorithm finds $\mathbf{r}$ such that $\mathsf{ok\_for}([0, n), \mathbf{r}, \mathsf{hints})$, which is the correctness condition above.
