# Change Log

Changes are listed most-recent-first.

## Changes made by Daira-Emma and Mary on 2023-03-15

* Make the instance entries just a flat vector.
* Improved consistency of notation.

## Changes made by Mary on 2023-28-03

* Added $q_v$ scaling functions to describe input to lookup tables.
* Completed first attempt at describing lookup constraints
* Have not yet tackled dynamic tables.

## Changes made by Daira-Emma and Str4d on 2023-03-17

* Rename some variables for consistency, and use $\triangledown$ also in Mary's definition of rotation constraints.
* Complete the "Greedy algorithm for choosing $\mathbf{r}$".
* Daira-Emma: Delete the paragraph describing the $\mathsf{Rot}$ constraints as hints, and add a note explaining the disadvantages of that approach.

## Changes made by Mary since 2023-15-03

* Add rotation constraints into copy constraints
  * This is an alternative proposal to Option B of the hint suggestion.
  * If we use this approach we could keep the description for copy constraints as is.

* Suggest enforcing that rotation constraints must be fully implied by $S_A$
    * Avoids having to define "used" cells and therefore simplifies.
    * We can use the (under construction) greedy algorithm anyway.

* Tried to be more precise about what $p_u$ constraints are valid.
    * Before we just said $p_u$ is constructed using addition and multiplication gates which is potentially too vague.
    * Current suggestion is a bit ugly and needs checking for correctness.

## Changes made by Daira-Emma since the 2023-03-03 meeting

* Change $S_A$ to an equivalence relation
  * This removes unnecessary degrees of freedom in specifying copy constraints between advice cells, and makes it easier to define correctness of the abstract $\rightarrow$ concrete compilation.
* Use $u$ instead of $k$ to index custom constraints, and $v$ instead of $k$ to index lookups.
  * This avoids overloading of $k$.
* Define the $\triangledown$ operator for addition modulo $n$.
* Define "used" cells.
* For "With rotations (option A)", change $E_u$ to be a list of rotations.
  * This avoids the need for $z_u$ as a separate variable.
* For "With rotations (option B)", give more detail and specify a correctness condition for compiling an abstract circuit to a concrete circuit using hints.

