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

* **Prove that the translation preserves correctness**, again intended for readers verifying the soundness of the optimizations.

## The Concrete Plonkish Relation

The relation $\cR_\concrete$ is an optimization of $\cR_\plonkish$.  We have highlighted differences using the icon ✨.

### Instances

$\cR_\concrete$ takes instances of the following form:

|   $\sf{Instance}$ | $\bs\sf{element}$                  | Description                                                                                          |
| -----------------:|:---------------------------------- |:---------------------------------------------------------------------------------------------------- |
|              $\F$ |                                    | A prime field.                                                                                       |
|               $C$ |                                    | The circuit.                                                                                         |
| $\hspace{3.3em}ϕ$ | $\oftype \F^{[C.t]}\hspace{4.8em}$ | The instance vector, where $C.t$ is the instance vector length defined below.                        |

The circuit $C \typecolon \ConcreteCircuit_{\F}$ in turn has the following form:

|    $\sf{Circuit}$ | $\bs\sf{element}$                  | Description                                                                                          | Used in                                   |
| -----------------:|:---------------------------------- |:---------------------------------------------------------------------------------------------------- |:----------------------------------------- |
|           $✨\;d$ | $\oftype \N$                       | Number of offsets.                                                                                   |                                           |
|    $✨\;\offsets$ | $\oftype \Set{\Z}$                 | Set of offsets of size $d$ enabling optimizations on the circuit structure.                          | [Custom constraints](#custom-constraints), [Lookup constraints](#lookup-constraints) |
|               $t$ | $\oftype \N$                       | Length of the instance vector.                                                                       |                                           |
|               $n$ | $\oftype \N \where n > 0$          | Number of rows for the witness matrix.                                                               |                                           |
|               $m$ | $\oftype \N^+$          | Number of columns for the witness matrix.                                                            |                                           |
|          $\equiv$ | $\oftype \Equiv{[m] \times [n]}$   | An equivalence relation indicating which witness entries must be equal to each other.                | [Copy constraints](#copy-constraints)     |
|               $S$ | $\oftype ([m] \times [n])^{[t]}$   | A vector indicating which witness entries are equal to instance vector entries.                      | [Copy constraints](#copy-constraints)     |
|             $m_f$ | $\oftype \N \where m_f ≤ m$        | Number of columns that are fixed.                                                                    | [Fixed constraints](#fixed-constraints)   |
|               $f$ | $\oftype \F^{[m_f \times n]}$      | The fixed content of the first $m_f$ columns.                                                        | [Fixed constraints](#fixed-constraints)   |
|         $✨\;p_u$ | $\oftype \F^{[m \cdot d]} \to \F$  | Custom multivariate polynomials.                                                                     | [Custom constraints](#custom-constraints) |
|          $\CUS_u$ | $\oftype \Set{[n]}$                | Sets indicating rows on which the custom polynomials $p_u$ are constrained to evaluate to $0$.       | [Custom constraints](#custom-constraints) |
|             $L_v$ | $\oftype \N$                       | Length of vectors in the lookup table with index $v$.                                                | [Lookup constraints](#lookup-constraints) |
|          $\TAB_v$ | $\oftype \Set{\F^{[L_v]}}$         | Lookup tables $\TAB_v$ each containing a set of vectors of type $\F^{[L_v]}$.                        | [Lookup constraints](#lookup-constraints) |
|     $✨\;q_{v,s}$ | $\oftype \F^{[m \cdot d]} \to \F$  | Scaling multivariate polynomials $q_{v,s}$ for $s \typecolon [L_v]$.                                 | [Lookup constraints](#lookup-constraints) |
|         $\LOOK_v$ | $\oftype \Set{[n]}$                | Sets indicating rows on which the scaling polynomials $q_{v,s}$ evaluate to some vector in $\TAB_v$. | [Lookup constraints](#lookup-constraints) |

Multivariate polynomials are defined below in the [Custom constraints](#custom-constraints) section.

### Witnesses

The relation $\cR_\concrete$ takes witnesses of the following form:

|    $\sf{Witness}$ | $\bs\sf{element}$                         | Description         |
| -----------------:|:----------------------------------------- |:------------------- |
| $\hspace{3.2em}w$ | $\oftype \F^{[m \times n]}\hspace{4.3em}$ | The witness matrix. |

✨ Define $\vec{w}_{j} \in \F^{[m \cdot d]}$ as the row vector
$\vec{w}_{j} := \vecof{w[i, j + \offset] \where (i, \offset) \gets [m] \times \offsets}$.

Some coordinates of $\vec{w}_j$ may involve out-of-bounds accesses to $w$, since $j$ ranges up to $n$ and $\offsets$ may include nonzero values. It is an error if a concrete circuit involves such accesses for *enabled* source rows of custom or lookup constraints — that is, if $j \in \CUS_u$ for any $u$ or $j \in \LOOK_v$ for any $v$.

### Definition of the relation

Given the above definitions, the relation $\cR_\concrete$ corresponds to a set of $\,(\!$ instance $\!,\,$ witness $\!)\,$ pairs
$$
 \left(x = \left(\F, C = \left(d, \offsets, t, n, m, \equiv, S, m_f, f, \vecof{(p_u, \CUS_{u}) \where u}, \vecof{(L_v, \TAB_v, \vecof{q_{v,s} \where s}, \LOOK_v) \where v}\right), ϕ\right),\, w \right)
$$
such that:
$$
\begin{array}{ll|l}
\hphantom{✨\;} w \typecolon \F^{[m \times n]}\comma f \typecolon \F^{[m_f \times n]} & & i \typecolon [m_f]\comma j \typecolon [n] \implies w[i, j] = f[i, j] \\[0.3ex]
\hphantom{✨\;} S \typecolon ([m] \times [n])^{[t]}\comma ϕ \typecolon \F^{[t]} & & k \typecolon [t] \implies w[S[k]] = ϕ[k] \\[0.3ex]
\hphantom{✨}   \equiv\,\,\typecolon \Equiv{[m] \times [n]} & & (i,j) \equiv (k,\ell) \implies w[i, j] = w[k, \ell] \\[0.3ex]
          ✨\;  \CUS_u \typecolon \Set{[n]}\comma p_u \typecolon \F^{[m \cdot d]} \to \F & & j \in \CUS_u \implies p_u(\vec{w}_j) = 0 \\[0.3ex]
          ✨\;  \LOOK_v \typecolon \Set{[n]}\comma q_{v,s} \typecolon \F^{[m \cdot d]} \to \F\comma \TAB_v \typecolon \Set{\F^{[L_v]}} & & j \in \LOOK_v \implies \vecof{q_{v,s}(\vec{w}_j) \where s \gets \range{0}{L_v}} \in \TAB_v
\end{array}
$$

In this model, a circuit-specific relation $\cR_{\F, C}$ for a field $\F$ and circuit $C$ is the relation $\cR_\plonkish$ restricted to $\{ ((\F, C, ϕ \typecolon \F^{[C.t]}), w \typecolon \F^{[C.m \times C.n]}) \}$.

### Conditions satisfied by statements in $\cR_\plonkish$

There are four types of constraints that a Plonkish statement $(x, w) \in \cR_\concrete$ must satisfy:

* Fixed constraints
* Copy constraints
* Custom constraints
* Lookup constraints

An Interactive Oracle Proof for an optimized Plonkish constraint system must demonstrate that all of these constraints are satisfied by $\,(\!$ instance $\!,\,$ witness $\!) \in \cR_\concrete$.

#### Fixed constraints

The first $m_f$ columns of $w$ are fixed to the columns of $f$.

#### Custom constraints

In the concrete model we define here, a custom constraint applies to a set of offset rows relative to each row selected for that constraint.

Custom constraints enforce that witness entries within a row satisfy some multivariate polynomial. Here $p_u$ could indicate any case that can be generated using a combination of multiplications and additions.

| Custom Constraints | Description |
| ------------------ |:----------- |
| $j \in \CUS_u \implies p_u(\vec{w}_j) = 0$ | $u$ is the index of a custom constraint. $j$ ranges over the set of rows $\CUS_u$ for which the custom constraint is switched on. |

Here $p_u \typecolon \F^{[m \cdot d]} \to \F$ is an arbitrary [multivariate polynomial](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)):

> Given $\eta$ symbols $X_i$ for $i \typecolon [\eta]$ called indeterminates, a multivariate polynomial $P$ in these indeterminates with coefficients in $\F$ is a finite linear combination
>
> $$P\!\left(\vecof{X_b \where b \gets \range{0}{\eta}}\right) = \sum_{z \stypecolon [\nu]} \Big(c_z \cdot \prod_{b \stypecolon [\eta]} X_b^{\alpha_{z,b}}\Big)$$
>
>  where $\nu \typecolon \N$, $c_z \typecolon \F \where c_z \neq 0$, and $\alpha_{z,b} \typecolon \N^+$.

Note that in this usage $\eta = m \cdot d$.

#### Lookup constraints

Lookup constraints enforce that the evaluation of some polynomial function on the witness entries $\vec{w}_j$ for the source row $j$ is contained in some table.
In this specification, we only support fixed lookup tables determined in advance. This could be generalized to support dynamic tables determined by part of the witness matrix.

| Lookup Constraints | Description |
| ------------------ |:----------- |
| $j \in \LOOK_v \implies\break \vecof{q_{v,s}(\vec{w}_j) \where s \gets \range{0}{L_v}} \in \TAB_v$ | $v$ is the index of a lookup table. $j$ ranges over the set of rows $\LOOK_v$ for which the lookup constraint is switched on. |

Here $q_{v,s} \typecolon \F^{[m \cdot d]} \to \F$ for $s \typecolon [L_v]$ are multivariate polynomials that collectively map the witness entries $\vec{w}_j$ on the lookup row $j \in \LOOK_v$ to a tuple of field elements. This tuple will be constrained to match some row of the table $\TAB_v$.

## Notation

If not otherwise defined, variable names used here are consistent with [the relation description](relation.md).

We will use the convention that variables marked with a prime ($'$) refer to *concrete* column or row indices.

For brevity when referring to variables dependent on an abstract circuit such as $C.t$, we will omit the $C.$ and just refer to $t$ when $C$ is obvious from context.

Similarly, when referring to variables dependent on a concrete circuit such as $C'.t'$, we will omit the $C'.$ and just refer to $t'$ when $C'$ is obvious from context.

An "abstract cell" specifies an entry in the witness matrix $w$ of the abstract circuit. A "concrete cell" specifies an entry in the witness matrix $w'$ of the concrete circuit.

We will denote the witness value at column $i$ and row $j$ as $w[i, j]$.

We say that an abstract cell with coordinates $(i, j)$ is "constrained" if it appears in some copy, custom, or lookup constraint. More precisely, $\constrained[i, j]$ is true iff any of the following hold:
$$
\begin{array}{rcl}
\exists (k, \ell) \neq (i, j) &:& (i, j) \equiv (k, \ell) \\
\exists k &:& S[k] = (i, j) \\
\exists u &:& j \in \CUS_u \and p_u(\vec{w}_j) \text{ ``has support involving'' } w[i, j] \\
\exists v, s &:& j \in \LOOK_v \and q_{v,s}(\vec{w}_j) \text{ ``has support involving'' } w[i, j],
\end{array}
$$

Here $p_u, \ q_{v,s} \typecolon \F^{[m]} \to \F$ are each multivariate polynomials as defined above in the [Custom constraints](#custom-constraints) section.

$P(\vec{w}_j)$ "has support involving" its variable at index $i$, that is $w[i, j]$, iff $\exists z \in [\nu] \suchthat \alpha_{z,i} > 0$.

## Correctness-preserving translation of circuits

We define a correctness-preserving translation of circuits—this serves as the security notion that our optimizations must satisfy to ensure they do not introduce vulnerabilities.

For simplicity fix a field $\F$. What we mean by a correctness-preserving translation $\cT \typecolon \AbstractCircuit_{\F} \to \ConcreteCircuit_{\F}$ is that $\cT$ is an efficiently computable function from abstract circuits to concrete circuits, such that for any abstract circuit $C$ with $C' = \cT(C)$:
  * There is a bijective map $\cI_C \typecolon \F^{[t]} \to \F^{[t']}$, efficiently computable in both directions, between abstract instances and concrete instances.
  * There is an efficient witness translation function $\cF_C \typecolon \F^{[m \times n]} \to \F^{[m' \times n']}$ from abstract witnesses to concrete witnesses.
  * Completeness is preserved: given a satisfying instance $x$ and witness $w$ for the abstract circuit $C$, $w' = \cF_C(w)$ is a satisfying witness for the concrete circuit $C'$ with instance $\cI_C(x)$.
  * Knowledge soundness is preserved: given a satisfying instance $x'$ and witness $w'$ for the concrete circuit $C'$, we can efficiently compute some satisfying witness $w$ for the abstract circuit $C$ with instance $\cI_C^{-1}(x')$.

We also claim that a correctness-preserving translation in this sense, when used with a concrete proof system that is zero-knowledge, necessarily yields an overall proof system for the abstract relation that is zero-knowledge. That is, informally, no additional information about the abstract witness is revealed beyond the fact that the prover knows such a witness.

> Aside: we could have required there to be an efficient reverse witness translation function $\cF'_C \typecolon \F_C^{[m' \times n']} \to \F_C^{[m \times n]}$ from concrete witnesses to abstract witnesses, and then used $w = \cF'_C(w')$ in the definition of knowledge soundness preservation. We do not take that approach because strictly speaking it would be an overspecification: we do not need the satisfying abstract witness to be *deterministically* and efficiently computable from the concrete witness; we only need it to be efficiently computable. Also, in general $w$ could also depend on the instance $x'$, not just $w'$. In practice, specifying such a function $\cF'_C$ is likely to be the easiest way to prove knowledge soundness preservation.

## Efficiency improvements achieved by the abstract-to-concrete translations

These translations aim to improve circuit efficiency in the following ways:

1) Reduce the number of concrete columns.  Each set of offset columns can be represented using a single concrete witness column.  The number of witness columns impacts the size of the resulting zero-knowledge proof.
2) Reduce the overall circuit area:  When offset [hints](#hints) identify abstract cells as equivalent, the backend can optimize layout by reordering rows so that equivalent cells overlap in the concrete matrix, minimizing unused space.

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

| Translation input  | Description                                                                                                  |
| ------------------ | ------------------------------------------------------------------------------------------------------------ |
| input circuit      | This is the instance excluding the instance vector $ϕ$.                                                      |
| offset hints       | $\vecof{(h_i, e_i) \typecolon [m'] \times \Z \where i \gets \range{0}{m}}$ provided by the circuit designer. |

| Translation output | Description                                                                                                  |
| ------------------ | ------------------------------------------------------------------------------------------------------------ |
| output circuit     | This is like the input circuit but also supports applying the polynomials to cells on offset rows.           |

### Adapting $\cR_\plonkish$ to concrete circuits

To translate from abstract Plonkish to concrete Plonkish circuits, we introduce the following high-level functions:
* $\translatecircuit$
* $\translateinstance$
* $\translatewitness$

Each of the functions $\translateinstance$, $\translatewitness$, and $\translatecircuit$ depends on a coordinate mapping function, $\coordmap$.

The function
$$
\coordmap \typecolon [m] \times [n] \to [m'] \times [n']
$$
is derived from design-time hints provided by the circuit author. To compute it, we define the function $\computecoordmap$.  Here $m'$ and $n'$ are the number of concrete rows and columns respectively, with $m' \leq m \and n' \geq n$.

### Function $\translatecircuit$ to translate the relation

The function
$$
\translatecircuit \typecolon \AbstractCircuit \times \Hints \to \ConcreteCircuit
$$
translates abstract Plonkish circuits to concrete Plonkish circuits.

Given $C \typecolon \AbstractCircuit$ and $\hints \typecolon \Hints$,
$$
\translatecircuit(C, \hints) = C' = \left(d', \offsets, t', n', m', \equiv, S, m_{f}', f', \vecof{(p_u, \CUS'_{u}) \where u}, \vecof{(L'_v, \TAB_v, \vecof{q'_{v,s} \where s}, \LOOK'_v) \where v}\right)
$$
where:
1) $(d', \offsets, m', n', \coordmap) := \computecoordmap(C, \hints)$
2) $t' := t$
3) $\equiv$
4) $S$
5) $m'_f$
6) $f'$
7) $
j' \in \CUS'_u \implies p_u\!\left(\vecof{w'[h_i, j' + e_i] \where i \gets \range{0}{m}}\right) = 0
$
8) $\CUS_u' :=  \setof{\mathbf{r}(j) \where j \in \CUS_u}$
9)  $L_v'$
10) $\TAB_v'$
11) $q_{v,s}'$
12) $\LOOK_v'$


## Computing the coordinate mapping $\coordmap$

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
                                 ^   ^
                                 |   |
                        +--------+   +-------+
                        |                    |
                   +---------+               |
                   | ok_for  |               |
                   +---------+               |
                      ^   ^                  |
                      |   |                  |
              +-------+   +-------------+    |
              |                         |    |
    +-------------------+         +----------------+
    | working_coord_map |         |  constrained   |
    +-------------------+         +----------------+
```


The function
$$
\computecoordmap \typecolon \AbstractCircuit \times \Hints \to \N \times \Z^{[d]} \times \N^+ \times \N \times \N^+ \times ([m] \times [n] \to [m'] \times [n'])
$$
takes as input an abstract circuit and a set of designer-provided hints $(C, \hints) \in \AbstractCircuit \times \Hints$.  The domain of abstract circuits, $\AbstractCircuit$, is defined formally in the description of the relation $\cR_\plonkish$.  The domain of offset hints, $\Hints$, is defined in the following section.

It returns $(d', \offsets', m', m_f', n', \coordmap)$ such that :
- $d' \in \N$ is the number of offsets
- $\offsets' \in \Z^{[d]}$ are the offsets
- $m' \in \N^+$ is the number of concrete columns,
- $m_f' \in \N \where m_f' \leq m'$ is the number of concrete columns that are fixed,
- $n' \in \N^+$ is the number of concrete rows,
- the coordinate mapping function
  $$
  \coordmap \typecolon [m] \times [n] \to [m'] \times [n']
  $$
  assigns concrete coordinates to each abstract cell position.

More specifically, to translate the abstract circuit to a concrete circuit using the hints $\vecof{(h_i, e_i) \where i}$, we construct an injective mapping of abstract row numbers to concrete row numbers before applying offsets, $\mathbf{r} \typecolon [n] \to [n']$ with $n' \geq n$, such that the abstract cell with coordinates $(i, j)$ maps to the concrete cell with coordinates $(h_i,\, \mathbf{r}(j) + e_i)$, where:
* all *constrained* abstract cells map to concrete cell coordinates that are in range;
* every *constrained* abstract cell is represented by a distinct concrete cell, except that abstract cells that are equivalent under $\equiv$ *may* be identified.

### Hints

The domain $\Hints$ represents collections of designer-provided **offset hints**. To simplify the programming model, the hints are not supposed to affect the meaning of a circuit (i.e. the set of public inputs for which it is satisfiable, and the knowledge required to find a witness).

Each hint assigns to a column index $i \in [m]$:

- a target column hint $h_i \in [m']$, and
- a row offset expression $e_i \in \Z$,

where for each column $i$ mapped to $h_i$, either $i$ and $h_i$ are both fixed abstract column indices $\in [m_f]$ or they are both non-fixed abstract column indices $\in [m_f, m)$.

We define:
$$
\Hints = \left\{ i \mapsto (h_i \typecolon [m], e_i \typecolon \Z) \where (i < m_f \and h_i < m'_f) \or (i \geq m_f \and h_i \geq m'_f) \right\}
$$
that is, the set of length-$m$ sequences
$$
\hints \typecolon [m] \to [m'] \times \Z
$$
where each entry $\hints[i]$ specifies a row hint and an offset for index $i$.

Thus, $\hints[i] = (h_i, e_i)$ specifies:
- $h_i \in [m']$: a column hint, representing a target column index
- $e_i \in \Z$: a row offset expression (e.g., a symbolic shift)

These hints guide the construction of the final coordinate map by specifying where (in columns) abstract elements prefer to appear and how to offset their placement in rows.

### Function $\computecoordmap$ to compute the coordinate mapping

The function $\computecoordmap$ computes the coordinate mapping $\coordmap$ used as a subroutine in $\translateinstance$, $\translatewitness$, and $\translatecircuit$.

It relies on two subroutines, whose input/output behavior is specified here. Their internal definitions will follow in subsequent sections.

- The function
  $$
  \constrained \typecolon \AbstractCircuit \times [m] \times [n] \to \setof{\false, \true}
  $$
  returns whether a cell $(i, j)$ is constrained — for example, if it lies in a fixed column or participates in a copy, custom, or lookup constraint.

- The function
  $$
  \okfor \typecolon \AbstractCircuit \times \Hints \times \setof{ R \subseteq [0, n) } \times ([n] \to [n']) \to \setof{\false, \true}
  $$
  returns whether the partial mapping $\mathbf{r}$ is valid for the set $R$ with respect to the given hints
  (see [here](#function-ok_for-to-check-if-current-offsets-are-ok) for the full definition of the function $\okfor$).

---

| $\computecoordmap(C, \hints))$ |
|-------------------------------------|
| set $\offsets := \setof{e_i \where (h_i, e_i) \in \hints}$ |
| set $d':=$ size of $\offsets$ |
| TODO: This is wrong, we need to eliminate unused columns instead of truncating them. set $m' := \max \setof{h_i \where (h_i, e_i) \in \hints}$ + 1 |
| set $\mathbf{r} := \{\}$ |
| set $a' := 0$ |
| for $g$ from $0$ to $n - 1$: |
| $\hspace{2em}$ find the minimal $g' \geq a' \suchthat \okfor(C, \hints, [g+1],\; \mathbf{r} \union \{ g \mapsto g' \} ) = \true$ |
| $\hspace{2em}$ set $\mathbf{r} := \mathbf{r} \union \{ g \mapsto g' \}$ and $a' := g' + 1$ |
| set $n' := \max \left\{\, \mathbf{r}(j) + e_i \where (i, j) \in [m] \times [n],\; \constrained(C, i, j) \,\right\} + 1$ |
| set $\coordmap \mathrel{\mathop:} [m] \times [n] \to [m'] \times [n'] \suchthat (i, j) \mapsto (h_i,\; \mathbf{r}(j) + e_i)$ |
| return ($d'$, $\offsets$, $m'$, $n'$, $\coordmap$)|

---

The algorithm computes:
- The set $\offsets$ of unique offsets $e_i$ appearing in the hints.
- The size $d'$ of the $\offsets$
- The number of concrete columns $m'$ as one more than the maximum $h_i$ appearing in the hints.
- A strictly increasing function $\mathbf{r} \typecolon [n] \to [n']$ that maps abstract to concrete row indices.
- The number of concrete rows $n'$ as one more than the maximum $\mathbf{r}(j) + e_i$ across all constrained cells $(i, j)$.

The mapping $\coordmap$ is then defined by:
$$
\coordmap(i, j) = (h_i,\; \mathbf{r}(j) + e_i)
$$

A greedy strategy is used to construct $\mathbf{r}$ incrementally while maintaining strict monotonicity. At each step, the algorithm selects the smallest $g' \geq a'$ such that extending $\mathbf{r}$ with $g \mapsto g'$ preserves the validity of all previous assignments, as checked by $\okfor$.

**Correctness guarantee.**

The algorithm always succeeds in finding such a $g'$ at each step. Since there is no upper bound on $g'$, we can always find one large enough to avoid conflicts. Specifically, when assigning $\mathbf{r}(g) = g'$, it suffices to ensure that:
$$
(h_i,\; g' + e_i) \neq (h_k,\; \mathbf{r}(\ell) + e_k)
$$
for all $\ell < g$ and all $i, k \in [m]$ such that both $(i, g)$ and $(k, \ell)$ are constrained. This ensures non-overlapping coordinate assignments for constrained cells.


### Function $\constrained$ to check if cells are constrained

We now define the function
$$
\constrained : \AbstractCircuit \times [m] \times [n] \to \setof{\true, \false}
$$
which was used in the $\computecoordmap$ algorithm to determine whether a given abstract cell $(i, j)$ must be assigned a coordinate in the final layout.

This function returns $\true$ if and only if the cell $w[i, j]$ is involved in any fixed value, equality, custom constraint, or lookup constraint.

---

In the abstract circuit $C \in \AbstractCircuit$, let each custom constraint polynomial $p_u \typecolon \F^m \to \F$ be written as
$$
p_u(\vec{w}_j) = \sum_{z=0}^{\nu - 1} \sum_{i=0}^{m - 1} \alpha_{u,z,i} \cdot m_{z,i}(\vec{w}_j),
$$
and similarly, each lookup constraint polynomial $q_{v,s} \typecolon \F^m \to \F$ is written as
$$
q_{v,s}(\vec{w}_j) = \sum_{z=0}^{\nu - 1} \sum_{i=0}^{m - 1} \beta_{v, s,z,i} \cdot n_{z,i}(\vec{w}_j),
$$
where $m_{z,i}$ and $n_{z,i}$ are monomials in the vector $\vec{w}_j$, and $\alpha_{u,z,i}, \beta_{v,s,z,i} \in \F$ are the corresponding coefficients.

___

| $\constrained(C, i, j )$ |
|-------------------------------------|
| check if $i < m_f$ |
| check if $\exists (k, \ell) \neq (i, j) \suchthat (i, j) \equiv (k, \ell)$ |
| check if $\exists k \suchthat S[k] = (i, j)$ |
| check if $\exists u \suchthat j \in \CUS_u$ and $\exists z \in [\nu] \suchthat \alpha_{u,z,i} > 0$ |
| check if $\exists v, s \where j \in \LOOK_v$ and $\exists z \in [\nu] \suchthat \beta_{v,s,z,i} > 0$ |
| if any check passes then return $\true$  |
| else return $\false$|

In other words, a cell $w[i, j]$ is considered constrained if it either contains a fixed value, participates in equality or permutation constraints, or contributes (with nonzero coefficient) to a custom or lookup constraint polynomial applied to column $j$.



### Function $\okfor$ to check if current offsets are OK.

We now define the function
$$
\okfor \typecolon \AbstractCircuit \times \Hints \times \{ R \subseteq [n] \} \times ([n] \to [n']) \to \setof{\false, \true}
$$
that returns whether the partial mapping $\mathbf{r}$ is valid for the set $R$ with respect to the given hints.

It relies on the subroutine
  $$
  \workingcoordmap \typecolon \Hints \times ([n] \to [n']) \times ([m] \times [n]) \to \N \times \N
  $$
that takes as input a set of hints, an offset function $\mathbf{r}$, and coordinates $(i,j)$ and behaves as follows

| $\workingcoordmap(\hints, \mathbf{r}, i, j )$ |
|-------------------------------------|
| set $(h_i, e_i) := \hints[i]$ |
| set $i' := h_i$ |
| set $j' := \mathbf{r}(j) + e_i$ |
| return $(i', j')$|



We now specify $\okfor$ that checks that constrained cells have unique coordinates in the concrete circuit.

| $\okfor(C, \hints, R, \mathbf{r})$ |
|------------------------------------|
| set $m' := \max \setof{h_i \where (h_i, e_i) \in \hints} + 1$|
| set $m:=$ the number of hints|
| for $(i,j) \in [m] \times R$ and for $(k, \ell) \in [m] \times R$: |
| $\hspace{2em}$ if $\constrained(C, i, j):$ |
| $\hspace{4em}$ check $\workingcoordmap(\hints, \mathbf{r}, i, j) \in [m'] \times \N$|
| $\hspace{4em}$ if $\constrained(C, k, \ell) \and (i,j) \neq (k, \ell):$|
| $\hspace{6em}$ check $\workingcoordmap(\hints, \mathbf{r}, i, j) \neq \workingcoordmap(\hints, \mathbf{r}, k, \ell)$|
| return $\true$ if all checks pass|
| else return $\false$|

We adopt the convention that indexing outside $w'$ results in an undefined value (i.e. the adversary could choose it).  Tesselation between custom constraints is represented by equivalence under $\equiv$.

Discussion: It is alright if one or more *unconstrained* abstract cells map to the same concrete cell as a constrained abstract cell, because that will not affect the meaning of the circuit. Notice that specifying $\equiv$ as an equivalence relation helps to simplify this definition (as compared to specifying it as a set of copy constraints), because an equivalence relation is by definition symmetric, reflexive, and transitive.



## Translating the circuits

We adopt the convention that indexing outside $w'$ results in an undefined value (i.e. the adversary could choose it).  Tesselation between custom constraints is represented by equivalence under $\equiv$.

A translation from an abstract to a concrete circuit takes the following inputs:

| Translation input  | Description |
| ------------------ | -------- |
| input circuit      | The abstract circuit, excluding the instance vector $ϕ$. |
| offset hints       | $\vecof{(h_i, e_i) \typecolon [m'] \times \Z \where i \gets \range{0}{m}}$ provided by the circuit designer. |

And produces:

| Translation output | Description |
| ------------------ | -------- |
| output circuit     | A version of the input circuit that supports assigning polynomials to cells on offset rows. |


In our model:

* The abstract witness matrix $w$ has $m$ abstract columns.
* The concrete witness matrix $w'$ has $m'$ columns, of which the first $m'_f$ are fixed.


### Witness translations

The constrained abstract cells $w \typecolon \F^{[m \times n]}$ are translated to concrete cells $w' \typecolon \F^{[m' \times n']}$:
$$
\constrained(i, j) \implies w'[\coordmap[i, j]] = w[i, j]
$$

The values of concrete cells not corresponding to any constrained abstract cell are arbitrary.

The fixed abstract cells $f \typecolon \F^{[m_f \times n]}$ are similarly translated to fixed concrete cells $f' \typecolon \F^{[m'_f \times n']}$:
$$
f'[\coordmap[i, j]] = f[i, j]
$$

Fixed concrete cells not assigned values by this translation are filled with zeros.

The abstract coordinates appearing in $\equiv$ and $S$ are similarly mapped to their concrete coordinates.

### Constraint translations

The conditions for custom constraints in the concrete circuit are then given by:
$$
\CUS'_u = \setof{\mathbf{r}(j) \where j \in \CUS_u} \\[0.6ex]
j' \in \CUS'_u \implies p_u\!\left(\vecof{w'[h_i, j' + e_i] \where i \gets \range{0}{m}}\right) = 0
$$

and similarly for lookups:
$$
\LOOK'_v = \setof{\mathbf{r}(j) \where j \in \LOOK_v} \\[0.6ex]
j' \in \LOOK'_v \implies \vecof{q_{v,s}\!\left(\vecof{w'[h_i, j' + e_i] \where i \gets \range{0}{m}}\right) \where s \gets \range{0}{L_v}} \in \TAB_v
$$



### Security proofs


Recall from the [relation definition](relation.md#copy-constraints) that fixed abstract cells with the same value are considered to be equivalent under $\equiv$. This allows a fixed column to be specified as a rotation of another fixed column, which can be useful to reduce the number of fixed concrete columns used by the concrete circuit.

Since correctness does not depend on the specific hints provided by the circuit programmer, it is also valid to use any subset of the provided hints, or to infer hints that were not provided.


* **Fixed-column consistency**: $i < m_f \implies h_i < m'_f$, i.e. the concrete circuit follows the same rule as the abstract circuit that fixed columns are on the left.
* **Semantics preservation**:  The hints do not affect the meaning of a circuit, i.e., the set of public inputs for which it is satisfiable, and the knowledge required to find a witness.
  <span style="color:red">Mary:  This is not concrete??? </span>



#### $\mathsf{FIND\_ROW\_MAPPING}$ gives a correctness-preserving translation

Recall from [Correctness-preserving translation of circuits](#correctness-preserving-translation-of-circuits) above that:

> What we mean by a correctness-preserving translation is that we know an efficient translation function from abstract circuits to concrete circuits, such that for any given translation:
>   * There is a bijective map $\cI \typecolon \F^{[t]} \to \F^{[t']}$, efficiently computable in both directions, between abstract instances and concrete instances.
>   * There is an efficient witness translation function $\cF \typecolon \F^{[m \times n]} \to \F^{[m' \times n']}$ from abstract witnesses to concrete witnesses.
>   * Completeness is preserved: given a satisfying instance $x$ and witness $w$ for the abstract circuit, $w' = \cF(w)$ is a satisfying witness for the concrete circuit with instance $\cI(x)$.
>   * Knowledge soundness is preserved: given a satisfying instance $x'$ and witness $w'$ for the concrete circuit, we can efficiently compute some satisfying witness $w$ for the abstract circuit with instance $\cI^{-1}(x')$.

Define $\cI(x) = x$, which is clearly invertible and efficiently computable in both directions.

The concrete witness $w' \typecolon \F^{m' \times n'}$ consists of the matrix of concrete values provided by the prover, as defined in [Preliminary definitions](#preliminary-definitions). Like the abstract witness, it consists of the (potentially private) prover inputs to the concrete circuit, and any intermediate values (including fixed values) that are not inputs to the concrete circuit but are required in order to satisfy it.

We now define our efficient abstract-to-concrete witness translation function $\cF$, which maps from the abstract witness $w$ to the concrete witness $w'$, by giving its value $\cF(w) = w'$ for every cell.

Let $n'$ and $m'$ be as defined by $\mathsf{FIND\_ROW\_MAPPING}$ above. Let $\coordmap$ be as defined in (1).

Let $\mathsf{inv\_coord\_map} \typecolon ([m'] \times [n']) \to \option{[m] \times [n]}$ be defined such that $\mathsf{inv\_coord\_map}[i', j']$ is the unique $(i, j) \in [m] \times [n] \suchthat \constrained[i, j]$ is true and $\coordmap[i, j] = (i', j')$, or $\bot$ if there is no such $(i, j)$.

Then let $\cF(w) = w'$ where
$$
w'[i', j'] = \begin{cases}
  w[\mathsf{inv\_coord\_map}[i', j']], &\text{if } \mathsf{inv\_coord\_map}[i', j'] \neq \bot \\
  0,                                   &\text{otherwise.}
\end{cases}
$$

This completely specifies $\cF$, and furthermore shows that $\cF$ is efficiently computable.

Note that $\mathsf{inv\_coord\_map}$ is well-defined because $\mathsf{FIND\_ROW\_MAPPING}$ ensures by construction that $\okfor([n], \mathbf{r}, \hints)$ holds, where
$$
\begin{array}{rcl}
\okfor(R, \mathbf{r}, \hints) &=& \forall i, k \typecolon [m],\, j, \ell \in R :\\[0.5ex]
&& \hspace{2em} (\constrained[i, j] \;\implies\; \coordmap[i, j] \in [m'] \times \N \;\and \\[0.3ex]
&& \hspace{2em} (\constrained[i, j] \and \constrained[k, \ell] \and (i, j) \not\equiv (k, \ell) \;\implies\; \coordmap[i, j] \neq \coordmap[k, \ell]) \\
\end{array}
$$

We can also define an efficient concrete-to-abstract witness translation function $\cF' \typecolon \F^{[m' \times n']} \to \F^{[m \times n]}$, by similarly giving its value for every cell:

Let $\cF'(w') = w$ where $w[i, j] = w'[\coordmap[i, j]]$.

(It happens that $\cF'$ as we have defined it here is a [left inverse](https://en.wikipedia.org/wiki/Inverse_function#Left_inverses) of $\cF$. This is not strictly necessary since the values of unconstrained abstract cells could be arbitrary.)

In order that $\mathsf{FIND\_ROW\_MAPPING}$ gives a correctness-preserving translation, it remains to show that:
1. Completeness is preserved: $\forall (x, w) \in \cR_\plonkish$, $(x', w') = (\cI(x), \cF(w)) = (x, \cF(w)) \in \cR_\concrete$.
2. Knowledge soundness is preserved: $\forall (x', w') \in \cR_\concrete$, we can efficiently compute $w = \cF'(w') \suchthat (\cI^{-1}(x'), w) = (x', w) \in \cR_\plonkish$.

For condition 1, we have $\forall (x, w) \in \cR_\plonkish$, which means that
$$
\begin{array}{ll|l}
   w \typecolon \F^{[m \times n]}, \ f \typecolon \F^{[m_f \times n]} & & i \in [m_f], \ j \in [n] \implies w[i, j] = f[i, j] \\[0.3ex]
   S \typecolon ([m] \times [n])^t, \ ϕ \typecolon \F^{[t]} & & k \in [t] \implies w[S[k]] = ϕ[k] \\[0.3ex]
   \equiv\; \typecolon \Equiv{[m] \times [n]} & & (i,j) \equiv (k,\ell) \implies w[i, j] = w[k, \ell] \\[0.3ex]
   \CUS_u \typecolon \Set{[n]}, \ p_u \typecolon \F^m \to \F & & j \in \CUS_u \implies p_u(\vec{w}_j) = 0 \\[0.3ex]
   \LOOK_v \typecolon \Set{[n]}, \ q_{v,s} \typecolon \F^m \to \F, \ \TAB_v \typecolon \Set{\F^{L_v}} & & j \in \LOOK_v \implies \vecof{q_{v,s}(\vec{w}_j) \where s \gets \range{0}{L_v}} \in \TAB_v
\end{array}
$$

We must prove that this implies $(x, \cF(w)) \in \cR_\concrete$, i.e.
$$
\begin{array}{ll|l}
   w' \typecolon \F^{[m' \times n']}, \ f' \typecolon \F^{m'_f \times n'} & & i' \in [m'_f], \ j' \in [n'] \implies w'[i', j'] = f[i', j'] \\[0.3ex]
   S' \typecolon ([m'] \times [n'])^t, \ ϕ \typecolon \F^{[t]} & & k \in [t] \implies w'[S'[k]] = ϕ[k] \\[0.3ex]
   \equiv'\; \typecolon \Equiv{[m'] \times [n']} & & (i',j') \equiv (k',\ell') \implies w'[i', j'] = w'[k', \ell'] \\[0.3ex]
   \CUS'_u \typecolon \Set{[n']}, \ p'_u \typecolon \F^{m'} \to \F & & j' \in \CUS'_u \implies p'_u(\vec{w}'_{j'}) = 0 \\[0.3ex]
   \LOOK'_v \typecolon \Set{[n']}, \ q'_{v,s} \typecolon \F^{m'} \to \F, \ \TAB_v \typecolon \Set{\F^{L_v}} & & j' \in \LOOK'_v \implies \vecof{q'_{v,s}(\vec{w}'_{j'}) \where s \gets \range{0}{L_v}} \in \TAB_v
\end{array}
$$

For condition 2, the abstract witness $w$ that we find will be $\cF'(x')$. Since $\cI$ is the identity function, we have that for any $(x', w') \typecolon \F^{[t]} \times \F^{[m' \times n']}$, $(\cI^{-1}(x'), \cF'(x')) = (x', w)$ exists and is efficiently computable. We must also prove that $(x', w') \in \cR_\concrete \implies (x', w) \in \cR_\plonkish$ (i.e. loosely speaking, the converse of what we need to prove for condition 1).

Given the definitions from [above](#constraint-translations), it is straightforward to see [FIXME] that in the statements to be proven for both conditions:

* the concrete fixed constraints for concrete fixed cells $(i',j')$ are in one-to-one correspondence with equivalent abstract fixed constraints for abstract cells $(i,j)$;
* the concrete input constraints for concrete cells $S'[k]$ for $k \typecolon [t]$ are in one-to-one correspondence with equivalent abstract input constraints for abstract cells $S[k]$ for $k \typecolon [t]$;
* the concrete equality constraints for concrete cells $(i',j') \equiv' (k',\ell')$ are in one-to-one correspondence with equivalent abstract equality constraints for abstract cells $(i,j) \equiv (k,\ell)$;
* the concrete custom constraints for concrete rows $j' \in \CUS'_u$, are in one-to-one correspondence with equivalent abstract custom constraints for abstract rows $j \in \CUS_u$;
* the concrete lookup constraints for concrete rows $j' \in \LOOK'_v$, are in one-to-one correspondence with equivalent abstract lookup constraints for abstract rows $j \in \LOOK_v$.

By "equivalent" here we mean that each concrete constraint is satisfied if and only if the corresponding abstract constraint is satisfied, given the above mappings between $(x, w)$ and $(x', w')$. Since the concrete and abstract constraints are also in one-to-one correspondence, all of the concrete constraints are satisfied if and only if all of the abstract constraints are satisfied.

The "if" direction implies condition 1, and the "only if" direction implies condition 2. Therefore, both completeness and knowledge soundness are preserved. $\blacksquare$
