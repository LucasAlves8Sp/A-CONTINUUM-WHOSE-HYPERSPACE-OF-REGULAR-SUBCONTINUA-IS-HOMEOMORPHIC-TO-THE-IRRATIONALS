# Research Project: The Possible Homeomorphism Types of Hyperspaces of Regular Subcontinua

## Role and objective

Act as an independent research mathematician specializing in continuum theory, hyperspace topology, and general topology.

Your task is to solve the open problem posed by Camargo, Ordoñez, and Ramírez in their 2024 paper *On the hyperspaces of meager and regular continua*.

Investigate whether there exists a metric continuum \(X\) whose hyperspace of regular subcontinua is homeomorphic to either the rational numbers \(\mathbb Q\) or the irrational numbers \(\mathbb I=\mathbb R\setminus\mathbb Q\).

Aim for an actual mathematical result: construct an example, prove an impossibility theorem, or establish a substantial new theorem that settles one of the two cases under a clearly defined and meaningful hypothesis.

Do not merely summarize the literature, restate known results, or create a list of speculative research directions. Investigate the exact problem, develop and test candidate constructions, and pursue a rigorous proof.

Be skeptical of every proposed construction and argument. Never report a problem as solved unless the construction or impossibility proof is complete.

## 1. Exact problem statement

A **continuum** is a nonempty compact connected metric space.

If \(X\) is a continuum, a subcontinuum \(A\subseteq X\) is called **regular** if it is regular closed in \(X\), meaning

\[
A=\overline{\operatorname{int}_X(A)}^{\,X}.
\]

Here, \(\operatorname{int}_X(A)\) and \(\overline{A}^{\,X}\) denote the interior and closure relative to \(X\).

Let \(C(X)\) be the hyperspace of all nonempty subcontinua of \(X\), equipped with the Hausdorff metric induced by a compatible metric on \(X\).

Define

\[
\mathcal D(X)=
\left\{
A\in C(X):
A=\overline{\operatorname{int}_X(A)}^{\,X}
\right\}.
\]

Equip \(\mathcal D(X)\) with the subspace topology inherited from \(C(X)\).

**The principal research question is:**

Does there exist a metric continuum \(X\) for which

\[
\mathcal D(X)\cong\mathbb Q,
\]

or one for which

\[
\mathcal D(X)\cong\mathbb I,
\qquad
\mathbb I=\mathbb R\setminus\mathbb Q?
\]

The symbol \(\cong\) means homeomorphism.

Treat these as two separate existence problems:

- **Problem Q:** Find a continuum \(X\) such that \(\mathcal D(X)\) is homeomorphic to \(\mathbb Q\), or prove that no such continuum exists.
- **Problem I:** Find a continuum \(X\) such that \(\mathcal D(X)\) is homeomorphic to \(\mathbb I\), or prove that no such continuum exists.

A construction solving either problem is already a successful outcome. It is not necessary to solve both.

## 2. Mandatory literature

Start with the original source of the questions and then examine the preceding theory. Do not assume the problems are still open without checking for subsequent work.

### Primary source

Javier Camargo, Norberto Ordoñez, and Diego Ramírez, *On the hyperspaces of meager and regular continua*, Applied General Topology 25 (2024), 385–406.

- [Official journal page and open PDF](https://polipapers.upv.es/index.php/AGT/article/view/20116)
- [Direct full-text PDF](https://riunet.upv.es/server/api/core/bitstreams/d9451d7e-69ec-4141-914f-58b0a541e526/content)
- [DOI: 10.4995/agt.2024.20116](https://doi.org/10.4995/agt.2024.20116)

**Read Section 3 carefully**, especially the results concerning the cardinality, compactness, and discreteness of \(\mathcal D(X)\), Theorem 3.25, and Question 3.26.

Understand the proofs, not just the statements. Record which features of a continuum determine the number of regular subcontinua, and which arguments constrain their possible topology.

### Foundational paper on regular subcontinua

Norberto Ordoñez, *The hyperspace of regular subcontinua*, Topology and its Applications 234 (2018), 415–427.

- [DOI: 10.1016/j.topol.2017.11.038](https://doi.org/10.1016/j.topol.2017.11.038)

Determine exactly which results about \(\mathcal D(X)\) are already available, especially the properties of \(\mathcal D(X)\) for locally connected continua and the compactness characterization.

### Further work on regular and meager subcontinua

Norberto Ordoñez, *Hyperspaces through regular and meager subcontinua*, Topology and its Applications 300 (2021), article 107760.

- [DOI: 10.1016/j.topol.2021.107760](https://doi.org/10.1016/j.topol.2021.107760)

Investigate its characterizations of continua through these hyperspaces and its open questions. Identify which techniques can be adapted to the present existence problem.

### Reference books

A. Illanes and S. B. Nadler Jr., *Hyperspaces: Fundamental and Recent Advances*, Marcel Dekker, 1999.

- [Publisher/book search](https://books.google.com/books?q=Illanes+Nadler+Hyperspaces+Fundamental+Recent+Advances)

S. B. Nadler Jr., *Continuum Theory: An Introduction*, Marcel Dekker, 1992.

- [Publisher/book search](https://books.google.com/books?q=Nadler+Continuum+Theory+An+Introduction)

S. Macías, *Topics on Continua*, second edition, Springer, 2018.

- [DOI: 10.1007/978-3-319-90902-8](https://doi.org/10.1007/978-3-319-90902-8)

Use these books to check standard facts and examples involving regular closed sets, decomposable and indecomposable continua, dendrites, and hyperspaces.

### Literature verification

Search for subsequent papers that cite the 2024 article, the 2018 article, and the 2021 article. Search exact formulations of both \(\mathcal D(X)\cong\mathbb Q\) and \(\mathcal D(X)\cong\mathbb I\).

Record the date of the search and distinguish:

- a question explicitly stated as open by its authors;
- a question for which no subsequent resolution was found;
- a question whose status has been verified through later sources.

Never infer current open status solely from the appearance of a question in the 2024 paper.

## 3. Establish the useful restrictions before constructing examples

Use the following known results to avoid wasting effort.

### Compactness

The literature establishes that

\[
\mathcal D(X)\text{ is compact}
\quad\Longleftrightarrow\quad
\mathcal D(X)\text{ is finite}.
\]

Both \(\mathbb Q\) and \(\mathbb I\) are noncompact. Therefore, this theorem does not settle either target, but it rules out arguments relying on \(\mathcal D(X)\) being an infinite compact space.

### Indecomposable continua

For an indecomposable continuum \(X\), every proper subcontinuum has empty interior, so

\[
\mathcal D(X)=\{X\}.
\]

Consequently, a solution must use a continuum for which regular proper subcontinua exist.

Do not spend time searching among indecomposable continua alone.

### Locally connected continua

For a locally connected continuum \(X\), the 2018 paper establishes that \(\mathcal D(X)\) is dense, contractible, and arcwise connected as a subspace of \(C(X)\).

Both \(\mathbb Q\) and \(\mathbb I\) are totally disconnected. Therefore, a locally connected continuum cannot furnish either target.

This is a crucial restriction: the construction should investigate **non-locally-connected continua**, while retaining enough structure to control their regular subcontinua.

### Countability and discreteness

The 2024 paper proves that \(\mathcal D(X)\) is never homeomorphic to \(\mathbb N\). It also establishes restrictions on possible finite cardinalities and gives conditions related to discreteness.

Do not confuse a space being countable with its being homeomorphic to \(\mathbb Q\). To realize \(\mathbb Q\), one must establish its actual topological structure, not merely its cardinality.

## 4. Main strategy: solve Problem Q first

Focus first on finding a continuum satisfying

\[
\mathcal D(X)\cong\mathbb Q.
\]

The rational numbers form a countable, metrizable, zero-dimensional space without isolated points.

This suggests a concrete plan:

1. Seek a continuum \(X\) with countably infinitely many regular subcontinua.
2. Determine whether \(\mathcal D(X)\) has isolated points.
3. If it is countable, metrizable, and has no isolated points, use the appropriate classical characterization of countable metrizable spaces to establish whether it is homeomorphic to \(\mathbb Q\).
4. If isolated points occur, determine whether they can be removed through a different construction or whether they are structurally unavoidable for a particular class of continua.

The central difficulty is Step 1. Do not assume that a continuum with countably many regular subcontinua exists merely because some finite cardinalities can occur.

### Construction direction A: decomposable continua assembled from simpler pieces

Investigate continua built by joining simpler continua at selected points or through structured decompositions.

For each proposed construction:

- characterize every subcontinuum with nonempty interior;
- determine exactly which of these are regular closed;
- check whether unions of adjacent pieces create additional regular subcontinua;
- prove that the list is exhaustive;
- calculate the Hausdorff topology on the resulting family.

A candidate construction is acceptable only if \(\mathcal D(X)\) is explicitly understood. A countable list of examples without an exclusion theorem is insufficient.

### Construction direction B: inverse limits

Consider inverse limits of finite graphs or finite continua with carefully chosen bonding maps.

Investigate whether the bonding maps can control the regular subcontinua of the limit so that:

- every regular subcontinuum is associated with a controlled finite-stage pattern;
- no unanticipated regular subcontinua arise in the inverse limit;
- the Hausdorff convergence relation among these sets gives the desired topology.

Prove the relationship between finite-stage data and regular subcontinua of the limit. Do not assume that regularity automatically passes through inverse limits.

### Construction direction C: continua with non-locally-connected structure

Investigate well-understood non-locally-connected continua and structured decompositions, including examples built from arcs or more complicated continua.

Avoid simply choosing a famous indecomposable continuum, since the preceding restriction immediately makes its regular-subcontinuum hyperspace trivial.

The aim is to identify a continuum that is sufficiently decomposable to have many regular subcontinua, but sufficiently non-locally-connected to avoid the arcwise-connectedness obstruction.

## 5. Then investigate Problem I

If Problem Q is settled, or if it reaches a genuine obstruction, investigate

\[
\mathcal D(X)\cong\mathbb I.
\]

The irrational numbers are homeomorphic to the Baire space \(\mathbb N^{\mathbb N}\). In particular, \(\mathbb I\) is metrizable, separable, completely metrizable, zero-dimensional, has no isolated points, and is nowhere locally compact.

These properties provide a diagnostic framework for a candidate \(\mathcal D(X)\).

Investigate whether a suitable continuum can have a regular-subcontinuum hyperspace with these properties. In particular:

- Can \(\mathcal D(X)\) be completely metrizable in its inherited topology?
- Is there a reason for \(\mathcal D(X)\) to be zero-dimensional?
- Can it have no isolated points?
- Can every point lack a compact neighborhood within \(\mathcal D(X)\)?

Because \(\mathcal D(X)\) sits inside the compact metric space \(C(X)\), complete metrizability of \(\mathcal D(X)\) is a strong constraint. Use the classical characterization of completely metrizable subspaces of metric spaces to determine what this implies about \(\mathcal D(X)\) as a subset of \(C(X)\).

Do not assume these properties can occur independently. If one of them is impossible for every regular-subcontinuum hyperspace, prove that obstruction and use it to rule out the target.

## 6. Look for a structural theorem, not only an example

If neither direct construction succeeds, identify and investigate a structural statement that would settle one branch.

Potential directions include:

- restrictions on the accumulation points of \(\mathcal D(X)\);
- conditions under which \(\mathcal D(X)\) has isolated points;
- whether countably infinite \(\mathcal D(X)\) must satisfy a particular decomposition or order property;
- whether the topology of \(\mathcal D(X)\) forces local compactness at some point;
- relationships between the topology of \(X\) and completeness or zero-dimensionality of \(\mathcal D(X)\).

These are candidate directions, not established facts. First inspect the 2018 and 2024 papers to determine which are already known.

Prioritize a structural theorem that directly addresses the rational or irrational homeomorphism type. Do not replace the target with an unrelated classification problem.

## 7. Proof requirements and counterexample testing

For every proposed \(X\), produce a precise description of \(\mathcal D(X)\).

The verification must include:

1. **Continuum verification:** prove that \(X\) is nonempty, compact, connected, and metrizable.
2. **Regularity verification:** identify the regular subcontinua using the equation
   \[
   A=\overline{\operatorname{int}_X(A)}^{\,X}.
   \]
3. **Exhaustiveness:** prove that all regular subcontinua have been found.
4. **Topology verification:** determine the topology induced by the Hausdorff metric, not merely the set-theoretic structure.
5. **Homeomorphism:** construct a homeomorphism to \(\mathbb Q\) or \(\mathbb I\), or invoke a classical characterization whose hypotheses have all been proved.
6. **Novelty check:** verify that the example or theorem is not already contained in the cited literature or an obvious consequence of a known result.

Actively try to break every construction. Search for additional regular subcontinua, unexpected limit points in \(\mathcal D(X)\), isolated points, compact neighborhoods, and failures of the claimed homeomorphism.

A counterexample to a proposed lemma should be retained as a useful result, not concealed.

## 8. Scope restrictions

Keep the investigation focused on the two stated homeomorphism types.

Do not divert into the general classification of hyperspaces, meager composants, filament composants, or cardinalities of \(\mathcal D(X)\), except when a specific theorem from those areas helps solve Problem Q or Problem I.

Do not spend the entire investigation restating existing definitions or reproving results that are already available in the primary sources.

Avoid making the project depend on additional set-theoretic assumptions unless the literature establishes that such assumptions are essential to the question.

Prefer explicit continua, precise structural lemmas, and directly relevant proofs over broad speculative frameworks.

## 9. Required report

Produce a research report containing:

### A. Status and literature

State the latest verified status of Problem Q and Problem I, with links to the original questions and any later relevant work.

### B. Selected target

Choose one branch as the primary objective. Explain why it offers the clearest route to a real result, based on the established theorems and constraints.

### C. Construction or obstruction

Give the strongest candidate construction or impossibility argument. Work through all key details rather than stopping at intuition.

### D. Rigorous mathematical progress

Prove every intermediate theorem used. If the original problem is solved, state the final theorem precisely and give a complete proof. If not, identify the exact mathematical obstruction preventing completion.

### E. Explicit next lemma

If the problem remains unsolved, formulate one narrow, verifiable lemma that would materially advance the chosen branch. Explain how proving it would lead toward the original question.

### F. References

List the sources actually used, with direct links and an explanation of which results from each source support the argument.

Maintain a proof ledger with the labels:

- **PROVED**
- **KNOWN FROM THE LITERATURE**
- **CONJECTURAL**
- **UNRESOLVED**

Do not describe a plausible construction as a counterexample until all the regular subcontinua and their induced topology have been determined.

The goal is to settle at least one of the two existence problems if possible, or to make precise mathematical progress toward a resolution. A correct impossibility theorem, a fully verified example, or a new structural obstruction is preferable to an unsupported claim of success.