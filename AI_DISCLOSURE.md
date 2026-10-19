# AI disclosure

*This is the AI disclosure of the paper, reproduced as it appears there. Section, theorem and
reference numbers refer to the paper; the cited references are listed at the end.*

This paper was prepared with substantial assistance from Claude Opus 5.5 (Anthropic). Most of the work was done jointly by the author and Claude. The author set the task, supplied the literature, gave the directions and provided feedback at each stage. Claude proposed the construction of Section 3, wrote the proofs and produced the Lean formalization.

The author proposed Question 3.26 of [1], posed earlier in [8, Pregunta 3.2.14], as the research target and gave a research plan:

- use the known restrictions on $\mathcal D(X)$ to rule out hopeless cases: $\mathcal D(X)$ compact only when finite, $\mathcal D(X)=\\{X\\}$ for indecomposable $X$, arcwise connected for locally connected $X$, never homeomorphic to $\mathbb N$;
- try the rational case through decomposable, inverse-limit or non-locally-connected constructions, and the irrational case through the classical characterization of the Baire space.

The manuscript then went through several rounds of feedback, each followed by a revision:

1. An audit of the first version found errors in a diameter estimate, a remark on a variant of the construction, an index in an example, and a planar realization. These were corrected and the proofs expanded.
2. The author found that the core-protection conjecture of the first version is false: the continuum of [8, Ejemplo 3.2.1], discussed in Section 6.3, violates it. The author then gave new directions:
   - remove the conjecture and the claims about the rational case;
   - instead, explain why the method does not apply to the rationals (Section 6);
   - compare the text directly with the literature.
3. The author revised the manuscript. An audit, checked by the author and Claude Opus 5.5, then led to corrections of wording and citations.
4. Later rounds of feedback from the author improved readability (figures and explanatory passages), completed the proof in Section 6.3, shortened Section 6.2 and filled small gaps in the exposition.

ChatGPT-Astra (OpenAI) was used, together with the author, to check successive versions of the manuscript and to send feedback.

Claude formalized the combinatorial core of the proof in Lean 4 (version 4.35.0) with Mathlib (commit `6015dbb`). The Lean source accompanies this paper as supplementary material; it builds with `lake build`, and `lake env lean CheckAxioms.lean` lists the axioms used. Sets of pieces are encoded as points of the Cantor cube $\\{0,1\\}^{\mathcal P}$, where $\mathcal P$ is the tree of Section 3.2 with its parent map; Lean indexes from $0$ rather than $1$, which only relabels the tree. Condition (c) of Theorem 4.6 is encoded without geometry: for a countable base $(V_j)$ of $K$, put $N_j=\\{k:a_k\in V_j\\}$; an included spine $S_{\beta,m}$ must have, for every $j$, infinitely many included children $B_{\beta^\frown(m,k)}$ with $k\in N_j$. This is equivalent to (c) because $K$ has no isolated points and the points $a_k$ are distinct. Without `sorry` or added axioms, Lean proves that the code space of admissible sets is a nonempty, zero-dimensional $G_\delta$ subset of the Cantor cube, that it is Polish, and that each of its compact subsets has empty interior; these are the code-space counterparts of Propositions 5.3 and 5.4. The statement $\mathcal D(X)\cong\mathbb N^{\mathbb N}$ of Theorem A is then derived from two results that are not formalized and enter as explicit hypotheses rather than axioms:

- the Alexandrov–Urysohn theorem [4, Theorem 7.7];
- the identification of $\mathcal D(X)$ with the code space (Theorem 4.6 and Proposition 5.2), the geometric core of the paper, whose proof uses the Knaster continuum and composants.

The final step $\mathbb N^{\mathbb N}\cong\mathbb I$ (Fact 2.5(c)) is classical and is not formalized. The file `SanityChecks.lean` checks the translation on small examples, and the development was also checked with the kernel replay tool `leanchecker` and with the independent type checker `nanoda`.

No independent expert has yet verified the proofs. The author takes full responsibility for the content.

---

**References cited above** (numbered as in the paper)

[1] J. Camargo, N. Ordoñez, and D. Ramírez, *On the hyperspaces of meager and regular continua*, Appl. Gen. Topol. **25** (2024), no. 2, 385–406. [doi:10.4995/agt.2024.20116](https://doi.org/10.4995/agt.2024.20116).

[4] A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics, vol. 156, Springer, New York, 1995.

[8] D. A. Ramírez Angarita, *Los hiperespacios de subcontinuos regulares y subcontinuos magros*, undergraduate thesis, Universidad Industrial de Santander, Bucaramanga, 2023. Available at <https://noesis.uis.edu.co/entities/publication/cd4f0fe6-ec75-47d8-8e0a-617149375321>.
