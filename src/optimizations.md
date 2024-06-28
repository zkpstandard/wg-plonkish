# Plonkish Backend Optimizations

## Background

The relation described in [Specification of the Plonkish Relation](relation.md) gives an abstract model of a Plonkish constraint system that is sufficiently expressive, but does not take into account some of the optimizations that are commonly used in Plonkish implementations, such as the use of offsets/rotations in Plonkish custom gates. The trade-off here is that the abstract model allows rows to be arbitrarily reordered.

> It would have been possible to directly include offsets in the constraint system model, but the most obvious ways of doing this would require the circuit programmer to think about copy constraints that don't naturally arise from the intended circuit definition.
>
> By separating the abstract constraint system from the concrete circuit, the programmer can instead locally add only the copy constraints that they know are needed. They are not forced to add artificial copy constraints corresponding to offsets. Although we still number the rows of the abstract witness matrix for convenience in the model, it would be sufficient to use any set with $n$ unique, not necessarily ordered elements. The abstract $\rightarrow$ concrete compilation can then reorder the rows as needed without changing the meaning of the circuit. This allows layout optimizations that would be impractical or error-prone to do manually, because they rely on global rather than local knowledge (such as which neighbouring cells are used or free, which can depend on gates that are logically unrelated).

## Preliminary definitions

If not otherwise defined, variable names used here are consistent with [the relation description](relation.md).

We will use the convention that variables marked with a prime ($'$) refer to *concrete* column or row indices.

An "abstract cell" or "concrete cell" specifies an entry in the witness matrix $w$ of the abstract circuit, or the witness matrix $w'$ of the concrete circuit, respectively.

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

## Compiling to a concrete circuit

$w$ represents $m$ _abstract_ columns, that do not directly correspond 1:1 to actual columns in the compiled circuit (but may do so if the backend chooses).

Offsets are represented by hints $\{ (h_i, e_i) \mathrel{⦂} [0,m') \times \mathbb{Z} \}_i$ where $m'$ is the number of concrete columns. To simplify the programming model, the hints are not supposed to affect the meaning of a circuit (i.e. the set of public inputs for which it is satisfiable, and the knowledge required to find a witness).

> TODO: should we only allow nonnegative $e_i$? That would simplify the correctness condition below.

Tesselation between custom constraints is just represented by equivalence under $\equiv$. When the offset hints indicate that two concrete cells in the same column are equivalent, the backend can optimise overall circuit area by reordering the rows so that the equivalent cells overlap.

More specifically, to compile the abstract circuit to a concrete circuit using the hints $\{ (h_i, e_i) \}_i$, we construct an injective mapping of abstract row numbers to concrete row numbers before applying offsets, $\mathbf{r} : [0, n) \mapsto [0, n')$ with $n' \geq n$, such that the abstract cell with coordinates $(i, j)$ maps to the concrete cell with coordinates $(h_i, \mathbf{r}(j) + e_i)$, where:
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

Then, $\mathbf{r}$ must be chosen such that $\mathsf{ok\_for}([0, n), \mathbf{r})$.

> It is alright if one or more *unconstrained* abstract cells map to the same concrete cell as a constrained abstract cell, because that will not affect the meaning of the circuit. Notice that specifying $\equiv$ as an equivalence relation helps to simplify this definition (as compared to specifying it as a set of copy constraints), because an equivalence relation is by definition symmetric, reflexive, and transitive.
>
> Recall from the [relation definition](relation.md#copy-constraints) that fixed abstract cells with the same value are considered to be equivalent under $\equiv$. This allows a fixed column to be specified as a rotation of another fixed column, which can be useful to reduce the number of fixed concrete columns used by the concrete circuit.

Since correctness does not depend on the specific hints provided by the circuit programmer, it is also valid to use any subset of the provided hints, or to infer hints that were not provided.

The constrained abstract cells $w : \mathbb{F}^{m \times n}$ are translated to concrete cells $w' : \mathbb{F}^{m' \times n'}$:
$$
\mathsf{constrained}(i, j) \Rightarrow w'[h_i, \mathbf{r}(j) + e_i] = w[i, j]
$$

The values of concrete cells not corresponding to any constrained abstract cell are arbitrary.

The fixed abstract cells $f : \mathbb{F}^{m_f \times n}$ are similarly translated to fixed concrete cells $f' : \mathbb{F}^{m_f \times n'}$:
$$
f'[h_i, \mathbf{r}(j) + e_i] = f[i, j]
$$

Fixed concrete cells not assigned values by this mapping are filled with zeros.

The abstract coordinates appearing in $\equiv$ and $S$ are similarly mapped to their concrete coordinates.

The conditions for custom gates in the concrete circuit are then given by:
$$
\mathsf{CUS}'_u = \{ \mathbf{r}(j) : j \in \mathsf{CUS}_u \} \\
j' \in \mathsf{CUS}'_u \Rightarrow p_u\left([w'[h_i, j' + e_i] : i \leftarrow 0 \text{..} m]\right) = 0
$$

and similarly for lookups:
$$
\mathsf{LOOK}'_v = \{ \mathbf{r}(j) : j \in \mathsf{LOOK}_v \} \\
j' \in \mathsf{LOOK}'_v \Rightarrow [q_{v,s}\left([w'[h_i, j' + e_i] : i \leftarrow 0 \text{..} m]\right) : s \leftarrow 0 \text{..} L_v] \in \mathsf{TAB}_v
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

The number of concrete rows is then given by $n' = \max \{ \mathbf{r}(j) + e_i : (i, j) \in ([0, m) \times [0, n)) \;\wedge\; \mathsf{constrained}(i, j) \} + 1$.

This algorithm is correct because in the last step it finds $\mathbf{r}$ such that $\mathsf{ok\_for}([0, n), \mathbf{r})$, which is the correctness condition above.

It is complete because for each step it is always possible to find a suitable $g'$: there is no upper bound on $g'$, and so we can always choose it large enough that any additional conditions of $\mathsf{ok\_for}([0, g], \mathbf{r} \cup \{g \mapsto g'\})$ relative to $\mathsf{ok\_for}([0, g-1], \mathbf{r})$ hold. Specifically: by symmetry it is sufficient to consider the additional conditions for which $j = g$ and $\ell < g$. There must be some $g' = \mathbf{r}(j)$ such that $(h_i, g' + e_i)$ does not overlap with $(h_k, \mathbf{r}(\ell) + e_k)$ for any $i, k \in [0, m)$ and $\ell \in [0, g-1]$.
