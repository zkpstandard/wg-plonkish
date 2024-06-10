# Plonkish Backend Optimizations

## Background

The relation described in [Specification of the Plonkish Relation](relation.md) gives an abstract model of a Plonkish constraint system that is sufficiently expressive, but does not take into account some of the optimizations that are commonly used in Plonkish implementations, such as the use of offsets/rotations in Plonkish custom gates. The tradeoff here is that the abstract model allows rows to be arbitrarily reordered.

> It would have been possible to directly include offsets in the constraint system model, but the most obvious ways of doing this would require the circuit programmer to think about copy constraints that don't naturally arise from the intended circuit definition.
>
> By separating the abstract constraint system from the concrete circuit, the programmer can instead locally add only the copy constraints that they know are needed. They are not forced to add artificial copy constraints corresponding to offsets. Although we still use numbered rows for convenience in the model, it would be sufficient to use any set with $n$ unique, not necessarily ordered elements. The abstract $\rightarrow$ concrete compilation can then reorder the rows as needed without changing the meaning of the circuit. This allows layout optimizations that would be impractical or error-prone to do manually, because they rely on global rather than local knowledge (such as which neighbouring cells are used or free, which can depend on gates that are logically unrelated).

## Compiling to a concrete circuit

TODO: define variables consistent with [the relation description](relation.md).

Below we will use the convention that variables marked with a prime ($'$) refer to *concrete* column or row indices.

We say that a cell with coordinates $(i, j)$ is ``constrained'' if it is in a fixed column or if it appears in some copy, custom, or lookup constraint. More precisely, $\mathsf{constrained}(i, j)$ is true iff any of the following hold:
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

----

$w$ represents $m$ _abstract_ columns, that do not directly correspond 1:1 to actual columns in the compiled circuit (but may do so if the backend chooses).

Offsets are represented by hints $\{ (h_i, e_i) \mathrel{⦂} [0,m') \times \mathbb{Z} \}_i$ where $m'$ is the number of concrete columns. To simplify the programming model, the hints are not supposed to affect the meaning of a circuit (i.e. the set of public inputs for which it is satisfiable, and the knowledge required to find a witness).

Tesselation between custom constraints is just represented by equivalence under $\equiv$. When the offset hints indicate that two cells in the same concrete column are equivalent, the backend can optimise overall circuit area by reordering the rows so that the equivalent cells overlap.

More specifically, to compile the abstract circuit to a concrete circuit using the hints $\{ (h_i, e_i) \}_i$, we construct an injective mapping of abstract row numbers to concrete row numbers before applying offsets, $\mathbf{r} : [0, n) \mapsto [0, n')$ with $n' \geq n$, such that the abstract cell with coordinates $(i, j)$ maps to the concrete cell with coordinates $(h_i, \mathbf{r}(j) + e_i)$, and all *constrained* abstract cells map to concrete cell coordinates that are in range.

In order for this compilation to be correct, we must choose $\mathbf{r}$ so that every *constrained* abstract cell is represented by a distinct concrete cell, except that abstract cells that are equivalent under $\equiv$ *may* be identified. That is, $\mathbf{r}$ must be chosen such that:
$$
\forall (i, j), (k, \ell) \in ([0, m) \times [0, n)) \times ([0, m) \times [0, n)) : \\
\mathsf{constrained}(i, j) \;\wedge\; \mathsf{constrained}(k, \ell) \;\wedge\; (i, j) \not\equiv (k, \ell) \Rightarrow (h_i, \mathbf{r}(j) + e_i) \neq (h_k, \mathbf{r}(\ell) + e_k)
$$

> It is alright if one or more *unconstrained* abstract cells map to the same concrete cell as a constrained abstract cell, because that will not affect the meaning of the circuit. Notice that specifying $\equiv$ as an equivalence relation helps to simplify this definition (as compared to specifying it as a set of copy constraints), because an equivalence relation is by definition symmetric, reflexive, and transitive.

Since correctness does not depend on the specific hints provided by the circuit programmer, it is also valid to use any subset of the provided hints, or to infer hints that were not provided.

The constrained abstract advice cells $w : \mathbb{F}^{m \times n}$ are translated to concrete advice cells $w' : \mathbb{F}^{m' \times n'}$:
$$
\mathsf{constrained}(i, j) \Rightarrow w'[h_i, \mathbf{r}(j) + e_i] = w[i, j]
$$

The values of concrete cells not corresponding to any constrained abstract cell are arbitrary.

The abstract fixed cells $f : \mathbb{F}^{m_f \times n}$ are similarly translated to concrete fixed cells $f' : \mathbb{F}^{m_f \times n'}$:
$$
f'[h_i, \mathbf{r}(j) + e_i] = f[i, j]
$$

Concrete fixed cells not assigned values by this mapping are filled with zeros.

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

There is a greedy algorithm for deterministically choosing $\mathbf{r}$ that maintains ordering of rows (i.e. $\mathbf{r}$ is strictly increasing), and simply inserts a gap in the row mapping whenever the above constraint would not be met for all rows so far:

For $g \in [0, n)$, define
$$
\begin{array}{rcl}
\mathsf{ok\_up\_to}(g, \mathbf{r}) &=& \forall (i, j), (k, \ell) \in ([0, m) \times [0, g]) \times ([0, m) \times [0, g]) :
\mathsf{constrained}(i, j) \;\wedge\; \mathsf{constrained}(k, \ell) \;\wedge\; (i, j) \not\equiv (k, \ell) \Rightarrow (h_i, \mathbf{r}(j) + e_i) \neq (h_k, \mathbf{r}(\ell) + e_k)
\end{array}
$$
That is, $\mathsf{ok\_up\_to}(g, \mathbf{r})$ means that the correctness criterion above holds for the subset $[0, g]$ of abstract rows.

| Algorithm for choosing $\mathbf{r}$ |
|----|
| set $\mathbf{r} := \{\}$ |
| set $v := 0$ |
| for $g$ from $0$ up to $n-1$: |
| $\hspace{2em}$ find the minimal $u \geq v$ such that $\mathsf{ok\_up\_to}(g, \mathbf{r} \cup \{g \mapsto u\})$ |
| $\hspace{2em}$ set $\mathbf{r} := \mathbf{r} \cup \{g \mapsto u\}$ and $v := u+1$ |
| let $n' = v$ be the number of concrete rows. |

This algorithm can be proven correct by induction on $n$. It is complete because for each step it is always possible to find a suitable $u$. That is, we can always choose $u$ large enough that any additional conditions
$$
\mathsf{constrained}(i, j) \;\wedge\; \mathsf{constrained}(k, \ell) \;\wedge\; (i, j) \not\equiv (k, \ell) \Rightarrow (h_i, \mathbf{r}(j) + e_i) \neq (h_k, \mathbf{r}(\ell) + e_k)
$$
for $j = g$ or $\ell = g$ are met, because $\mathbf{r}(g) = u$ and both $(h_i, \mathbf{r}(j) + e_i)$ and $(h_k, \mathbf{r}(\ell) + e_k)$ can be made not to overlap with any previously constrained cell.
