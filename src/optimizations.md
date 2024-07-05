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

We say that an abstract cell with coordinates $(i, j)$ is "constrained" if it is in a fixed column or if it appears in some copy, custom, or lookup constraint. More precisely, $\mathsf{constrained}(i, j)$ is true iff any of the following hold:
$$
\begin{array}{rcl}
&& i < m_f \\
\exists (k, \ell) \neq (i, j) &:& (i, j) \equiv (k, \ell) \\
\exists k &:& ((i, j), k) \in S \\
\exists u &:& j \in \mathsf{CUS}_u \text{ and } w[i, j] \text{ ``might be used'' in } p_u(\vec{w}_j) \\
\exists v, s &:& j \in \mathsf{LOOK}_v \text{ and } w[i, j] \text{ ``might be used'' in } q_{v,s}(\vec{w}_j),
\end{array}
$$

Here $p_u, \ q_{v,s} \mathrel{⦂} \mathbb{F}^m \mapsto \mathbb{F}$ are each [multivariate polynomials](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)) as defined in the relation description:

> Given $\eta$ symbols $X_0, \dots, X_{\eta-1}$ called indeterminates, a multivariate polynomial $P$ in these indeterminates, with coefficients in $\mathbb{F}$,
> is a finite linear combination $$P(X_0, \dots, X_{\eta-1}) = \sum_{z=0}^{\nu-1} \Big(c_z\, {\small\prod_{b=0}^{\eta-1}}\, X_b^{\alpha_{z,b}}\Big)$$ where $\nu \mathrel{⦂} \mathbb{N}$, $c_z \mathrel{⦂} \mathbb{F}$, and $\alpha_{z,b} \mathrel{⦂} \mathbb{N}$.

Cell $w[i, j]$ "might be used" in $P(\vec{w}_j)$ iff $\exists z \in [0, \nu)$ s.t. $\alpha_{z,i} > 0$.

## Correctness-preserving translation of circuits

What we mean by a correctness-preserving translation is that we know an efficient translation function from abstract circuits to concrete circuits, such that for any given translation:
  * There is a bijective map $\mathcal{I}$, efficiently computable in both directions, between abstract instances and concrete instances.
  * There an efficient witness translation function $\mathcal{F}$ from abstract witnesses to concrete witnesses.
  * Completeness is preserved: given a satisfying instance $x$ and witness $w$ for the abstract circuit, $w' = \mathcal{F}(w)$ is a satisfying witness for the concrete circuit with instance $\mathcal{I}(x)$.
  * Knowledge soundness is preserved: given a satisfying instance $x$ and witness $w'$ for the concrete circuit, we can efficiently compute some satisfying witness $w$ for the abstract circuit with instance $\mathcal{I}^{-1}(x)$.

We also claim that a correctness-preserving translation in this sense, when used with concrete proof system that is zero-knowledge, necessarily yields an overall proof system for the abstract relation that is zero-knowledge. That is, informally, no additional information about the abstract witness is revealed beyond the fact that the prover knows such a witness.

## A model for a class of abstract-to-concrete translations and their correctness

We give a specific model for a family of translations, and a criterion for them to be correctness-preserving consistent with the above definition. Note that this is very far from covering all possible correctness-preserving translations.

In our model, a translation from an abstract to a concrete circuit will take inputs of the following form:

| Translation input  | Description |
| ------------------ | -------- |
| input circuit      | This is the instance excluding the instance vector $\phi$. |
| offset hints       | $\big[\, (h_i, e_i) \mathrel{⦂} [0,m') \times \mathbb{Z} \,:\, i \leftarrow 0 \text{..} m \,\big]$ provided by the circuit designer. |

| Translation output | Description |
| ------------------ | -------- |
| output circuit     | We don't have a definition of this yet. It is like the input circuit but also supports applying the polynomials to cells on offset rows. |

The abstract witness matrix $w$ consists of $m$ abstract columns.

Offsets are represented by hints $\big[\, (h_i, e_i) \mathrel{⦂} [0,m') \times \mathbb{Z} \,:\, i \leftarrow 0 \text{..} m \,\big]$ where $m'$ is the number of concrete columns. To simplify the programming model, the hints are not supposed to affect the meaning of a circuit (i.e. the set of public inputs for which it is satisfiable, and the knowledge required to find a witness).

> TODO: should we only allow nonnegative $e_i$? That would simplify the correctness condition below.

Tesselation between custom constraints is just represented by equivalence under $\equiv$. When the offset hints indicate that two concrete cells in the same column are equivalent, the backend can optimize overall circuit area by reordering the rows so that the equivalent cells overlap.

More specifically, to translate the abstract circuit to a concrete circuit using the hints $\big[\, (h_i, e_i) \,\big]_i$, we construct an injective mapping of abstract row numbers to concrete row numbers before applying offsets, $\mathbf{r} : [0, n) \mapsto [0, n')$ with $n' \geq n$, such that the abstract cell with coordinates $(i, j)$ maps to the concrete cell with coordinates $(h_i, \mathbf{r}(j) + e_i)$, where:
* all *constrained* abstract cells map to concrete cell coordinates that are in range;
* every *constrained* abstract cell is represented by a distinct concrete cell, except that abstract cells that are equivalent under $\equiv$ *may* be identified.

That is: for $R \subseteq [0, n)$ define
$$
\begin{array}{rcl}
\mathsf{ok\_for}(R, \mathbf{r}) &=& \forall (i, j), (k, \ell) \in ([0, m) \times R) \times ([0, m) \times R) :\\[0.5ex]
&& \hspace{2em} (\mathsf{constrained}(i, j) \;\Rightarrow\; \mathbf{r}(j) + e_i \geq 0) \;\;\wedge\; \\[0.3ex]
&& \hspace{2em} (\mathsf{constrained}(i, j) \;\wedge\; \mathsf{constrained}(k, \ell) \;\wedge\; (i, j) \not\equiv (k, \ell) \;\Rightarrow\; (h_i, \mathbf{r}(j) + e_i) \neq (h_k, \mathbf{r}(\ell) + e_k)) \\
\end{array}
$$

Then, the overall correctness condition is that $\mathbf{r}$ must be chosen such that $\mathsf{ok\_for}([0, n), \mathbf{r})$. We claim that this implies the more general definition of correctness preservation for this family of translations.

> Proof sketch [TODO remove handwaving]:
>
> $\mathcal{I}$ is the identity function and $\mathcal{F}$ is described below. $\mathcal{F}$, $\mathcal{I}$, and $\mathcal{I}^{-1}$ are obviously efficiently computable. Given that the concrete custom constraints and lookups are just the abstract constraints and lookups modified to access the same witness values in their translated locations, preservation of completeness preservation follows immediately. Preservation of knowledge soundness holds because, informally, we can invert the coordinate translation defined by $\mathcal{F}$ to reconstruct all of the abstract witness cells that are needed to satisfy the abstract relation.

Discussion: It is alright if one or more *unconstrained* abstract cells map to the same concrete cell as a constrained abstract cell, because that will not affect the meaning of the circuit. Notice that specifying $\equiv$ as an equivalence relation helps to simplify this definition (as compared to specifying it as a set of copy constraints), because an equivalence relation is by definition symmetric, reflexive, and transitive.

Recall from the [relation definition](relation.md#copy-constraints) that fixed abstract cells with the same value are considered to be equivalent under $\equiv$. This allows a fixed column to be specified as a rotation of another fixed column, which can be useful to reduce the number of fixed concrete columns used by the concrete circuit.

Since correctness does not depend on the specific hints provided by the circuit programmer, it is also valid to use any subset of the provided hints, or to infer hints that were not provided.

### Witness translations

The constrained abstract cells $w : \mathbb{F}^{m \times n}$ are translated to concrete cells $w' : \mathbb{F}^{m' \times n'}$:
$$
\mathsf{constrained}(i, j) \Rightarrow w'[h_i, \mathbf{r}(j) + e_i] = w[i, j]
$$

The values of concrete cells not corresponding to any constrained abstract cell are arbitrary.

The fixed abstract cells $f : \mathbb{F}^{m_f \times n}$ are similarly translated to fixed concrete cells $f' : \mathbb{F}^{m_f \times n'}$:
$$
f'[h_i, \mathbf{r}(j) + e_i] = f[i, j]
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

### Greedy algorithm for choosing $\mathbf{r}$

There is a greedy algorithm for deterministically choosing $\mathbf{r}$ that maintains ordering of rows (i.e. $\mathbf{r}$ is strictly increasing), and simply inserts a gap in the row mapping whenever the above constraint would not be met for all rows so far.

| Algorithm for choosing $\mathbf{r}$ |
|----|
| set $\mathbf{r} := \{\}$ |
| set $a' := 0$ |
| for $g$ from $0$ up to $n-1$: |
| $\hspace{2em}$ find the minimal $g' \geq a'$ such that $\mathsf{ok\_for}([0, g], \mathbf{r} \cup \{g \mapsto g'\})$ |
| $\hspace{2em}$ set $\mathbf{r} := \mathbf{r} \cup \{g \mapsto g'\}$ and $a' := g'+1$ |

The number of concrete rows is then given by $n' = \max \big\{\, \mathbf{r}(j) + e_i : (i, j) \in ([0, m) \times [0, n)) \;\wedge\; \mathsf{constrained}(i, j) \,\big\} + 1$.

This algorithm is correct because in the last step it finds $\mathbf{r}$ such that $\mathsf{ok\_for}([0, n), \mathbf{r})$, which is the correctness condition above.

It is complete because for each step it is always possible to find a suitable $g'$: there is no upper bound on $g'$, and so we can always choose it large enough that any additional conditions of $\mathsf{ok\_for}([0, g], \mathbf{r} \cup \{g \mapsto g'\})$ relative to $\mathsf{ok\_for}([0, g-1], \mathbf{r})$ hold. Specifically: by symmetry it is sufficient to consider the additional conditions for which $j = g$ and $\ell < g$. There must be some $g' = \mathbf{r}(j)$ such that $(h_i, g' + e_i)$ does not overlap with $(h_k, \mathbf{r}(\ell) + e_k)$ for any $i, k \in [0, m)$ and $\ell \in [0, g-1]$.
