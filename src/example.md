# Example: Luhn algorithm

This page provides a detailed walkthrough of building a Plonk constraint system using the Luhn algorithm as an example. We will demonstrate how to represent a simple computation as a circuit and how to apply different types of Plonk constraints: copy constraints, lookup constraints and custom constraints.

## Luhn algorithm

The Luhn algorithm is a check digit formula used to validate identification numbers such as credit card numbers or national identification numbers. It works as follows:

1. Split the number into a payload (all digits except the last one) and a given check digit (the last digit).
2. Compute what the check digit should be from the payload:

   a. Starting from the right of the payload (which does not include the check digit), double every second digit starting with the rightmost. That is, double the rightmost, third-rightmost, fifth-rightmost, etc. digits of the payload. If doubling results in a number greater than 9, subtract 9.

   b. Let $s$ be the sum of all the digits (transformed or not) resulting from step a.

   c. The check digit is computed as $(10 - (s \bmod 10)) \bmod 10$.

3. Compare the computed check digit with the given check digit. If they match, the number is valid.

**Example:** Let’s validate the account number $13893722978$.
For this account number, the payload is $1389372297$ and the check digit is $8$.

| Payload | Transformed value |
| :-----: | :---------------: |
|    7    |         5         |
|    9    |         9         |
|    2    |         4         |
|    2    |         2         |
|    7    |         5         |
|    3    |         3         |
|    9    |         9         |
|    8    |         8         |
|    3    |         6         |
|    1    |         1         |

Sum: $s = 5+9+4+2+5+3+9+8+6+1 = 52$

Check digit: $(10 - (52 \bmod 10 )) \bmod 10 = 8$

The number is valid.

## Plonk constraint system construction

We will model the Luhn algorithm in a Plonk constraint system. For simplicity, we assume a fixed-length input $11$ digits where the first $10$ digits are the private payload and the last one is the public check digit.

### Instance elements

We work over the prime field $\mathbb{F}_{101}$ (which ensures that $s$ can be represented without overflow).

We have a single instance value ($t=1$): the check digit.

### Witness matrix

The witness matrix will contain:

- the payload $[a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9]$
- the transformed digits for every second digit in the payload $[b_1, b_3, b_5, b_7, b_9]$:
  $$
  \forall i \in [0..4], b_{2 \cdot i +1} = \begin{cases}
  2 \cdot a_{2 \cdot i +1} & \text{ if } 2 \cdot a_{2 \cdot i +1} < 9 \\
  2 \cdot a_{2 \cdot i +1} - 9 & \text{ otherwise}
  \end{cases}
  $$
- the sum of all digits $s$ and some intermediate sums $s_0$ and $s_1$. These intermediate sums help optimize the layout of the witness matrix layout.
$$
\begin{cases}
s_0 &= b_1 + a_0 + a_2 + a_4 \\
s_1 &= b_3 + a_6 + a_8 + s_0 \\
s &=  b_5 + b_7 + b_9 + s_1 = a_0 + b_1 + a_2 + b_3 + a_4 + b_5 + a_6 + b_7 + a_8 + b_9
\end{cases}
$$
- the quotient $q$ and the remainder $r$ of the division of $s$ by 10
$$s=10 \cdot q + r$$
- the check digit $c$

Witness matrix layout:
| $w[0, j]$ | $w[1, j]$ | $w[2, j]$ | $w[3, j]$ | $w[4, j]$ | $w[5, j]$ |
|:---------:|:---------:|:---------:|:---------:|:---------:|:---------:|
| $a_1$ | $b_1$ | $a_0$ | $a_2$ | $a_4$ | $s_0$ |
| $a_3$ | $b_3$ | $a_6$ | $a_8$ | $s_0$ | $s_1$ |
| $a_5$ | $b_5$ | $b_7$ | $b_9$ | $s_1$ | $s$ |
| $a_7$ | $b_7$ | $s$ | $q$ | $r$ | $c$ |
| $a_9$ | $b_9$ | | | | |

**Witness matrix for $13893722978$:**
Let’s rewrite the witness matrix for the payload $13893722978$

- Payload: $[a_0, a_1, ..., a_9] = [1, 3, 8, 9, 3, 7, 2, 2, 9, 7]$
- Transformed digits
  $$
  \begin{cases}
  b_1 = 2 \cdot a_1 = 2 \cdot 3 = 6 \\
  b_3 = 2 \cdot a_3 = 2 \cdot 9 = 18 \rightarrow 9 \\
  b_5 = 2 \cdot a_5 = 2 \cdot 7 = 14 \rightarrow 5 \\
  b_7 = 2 \cdot a_7 = 2 \cdot 2 = 4 \\
  b_9 = 2 \cdot a_9 = 2 \cdot 7 = 14 \rightarrow 5
  \end{cases}
  $$
- Sums
  $$
  \begin{cases}
  s_0 = 6+1+8+3 = 18 \\
  s_1 = 9+2+9+18 = 38 \\
  s = 5+4+5+38 = 52
  \end{cases}
  $$
- The division of $s$ by $10$
  $$
  s = 10 \cdot q + r \text{ with } \begin{cases}
  s=52 \\
  q=5 \\
  r=2
  \end{cases}
  $$
- Check digit
  $$c=10-r=10-2=8$$

Witness matrix layout:
| $w[0, j]$ | $w[1, j]$ | $w[2, j]$ | $w[3, j]$ | $w[4, j]$ | $w[5, j]$ |
|:---------:|:---------:|:---------:|:---------:|:---------:|:---------:|
| $3$ | $6$ | $1$ | $8$ | $3$ | $18$ |
| $9$ | $9$ | $2$ | $9$ | $18$ | $38$ |
| $7$ | $5$ | $4$ | $5$ | $38$ | $52$ |
| $2$ | $4$ | $52$ | $5$ | $2$ | $8$ |
| $7$ | $5$ | | | | |

## Copy constraints

Copy constraints enforce that entries in the witness matrix are equal to each other, or that an instance entry is equal to a witness entry.

We have the following copy constraints

- $S = {((5, 3), 0)}$ to enforce that the witness value $w[5, 3]$ must be equal to the first instance value (the given check digit)
- $(5, 0) \equiv (4, 1)$ for $s_0$
- $(5, 1) \equiv (4, 2)$ for $s_1$
- $(1, 3) \equiv (2, 2)$ for $b_7$
- $(1, 4) \equiv (3, 2)$ for $b_9$
- $(5, 2) \equiv (2, 3)$ for $s$

## Lookup constraints

Lookup constraints enforce that some polynomial function of the witness entries on a row are contained in some table.

Some cells are constrained to values in the range $[0, 9]$:

- The payload: all $a_i$
- The transformed digits: all $b_i$
- The quotient $q$ and the remainder $r$ of the division of $s$ by $10$

For duplicated cells such as $s_0$, it is sufficient to constrain only one occurrence.

Those cells are blue in the following witness matrix:

|     $w[0, j]$      |     $w[1, j]$      |     $w[2, j]$      |     $w[3, j]$      |     $w[4, j]$      | $w[5, j]$ |
| :----------------: | :----------------: | :----------------: | :----------------: | :----------------: | :-------: |
| $\color{blue} a_1$ | $\color{blue} b_1$ | $\color{blue} a_0$ | $\color{blue} a_2$ | $\color{blue} a_4$ |   $s_0$   |
| $\color{blue} a_3$ | $\color{blue} b_3$ | $\color{blue} a_6$ | $\color{blue} a_8$ |       $s_0$        |   $s_1$   |
| $\color{blue} a_5$ | $\color{blue} b_5$ |       $b_7$        |       $b_9$        |       $s_1$        |    $s$    |
| $\color{blue} a_7$ | $\color{blue} b_7$ |        $s$         |  $\color{blue} q$  |  $\color{blue} r$  |    $c$    |
| $\color{blue} a_9$ | $\color{blue} b_9$ |                    |                    |                    |           |

More precisely, the lookup constraints are

$$
\begin{cases}
L_0 = 1, &TAB_0 = \{0..9\}, &q_{0,0} = X_0, &LOOK_0 = \{0..4\} \\
L_1 = 1, &TAB_1 = \{0..9\}, &q_{1,0} = X_1, &LOOK_1 = \{0..4\} \\
L_2 = 1, &TAB_2 = \{0..9\}, &q_{2,0} = X_2, &LOOK_2 = \{0..1\} \\
L_3 = 1, &TAB_3 = \{0..9\}, &q_{3,0} = X_3, &LOOK_3 = \{0, 1, 3\} \\
L_4 = 1, &TAB_4 = \{0..9\}, &q_{4,0} = X_4, &LOOK_4 = \{0, 3\}
\end{cases}
$$

**Note:** No lookup constraint is needed for $c$ since:

- It is equal to a public input (copy constraint).
- By definition, $c=10-r$ and $r \in [0, 9]$. So, $c \in [0, 9]$.

## Custom constraints

Custom constraints enforce that witness entries within a row satisfy some multivariate polynomial.

With custom constraints, we enforce that

1. The transformed digits are valid. It means that $\forall i \in [0..4]$, $b_{2 \cdot i +1}$ is equal to either $(2 \cdot a_{2 \cdot i +1})$ or $(2 \cdot a_{2 \cdot i +1}) - 9$. So, $$\forall i \in [0..4], (2 \cdot a_{2 \cdot i +1} - b_{2 \cdot i +1}) (2 \cdot a_{2 \cdot i +1} -9 - b_{2\cdot i +1}) = 0$$
This constraint is sufficient to ensure the validity of the transformed digits, because the lookup constraints ensure they are valid digits.

Thus, the custom constraint for transformed digits is:

$$
\begin{cases}
p_0(X_0, ..., X_5) = (2 \cdot X_0 - X_1) (2 \cdot X_0 - 9 - X_1) \\
CUS_0 = \{0..4\}
\end{cases}
$$

2. The sums are valid

$$
\begin{cases}
s_0 &= b_1 + a_0 + a_2 + a_4 \\
s_1 &= b_3 + a_6 + a_8 + s_0 \\
s &=  b_5 + b_7 + b_9 + s_1
\end{cases}
$$

Thus, the custom constraint for sums is:

$$
\begin{cases}
p_1(X_0, ..., X_5) = X_1 + X_2+ X_3+ X_4 -X_5\\
CUS_1 = \{0..2\}
\end{cases}
$$

3. The division is correct

$$s = 10 \cdot q + r$$

Thus, the custom constraint for the division is:

$$
\begin{cases}
p_2(X_0, ..., X_5) = 10 \cdot X_3 + X_4 - X_2\\
CUS_2 = \{3\}
\end{cases}
$$

4. The computed check digit is correct: $c=10-r$.

Thus, the custom constraint for check digit is:

$$
\begin{cases}
p_3(X_0, ..., X_5) = (10 - X_4 - X_5)\\
CUS_3 = \{3\}
\end{cases}
$$
