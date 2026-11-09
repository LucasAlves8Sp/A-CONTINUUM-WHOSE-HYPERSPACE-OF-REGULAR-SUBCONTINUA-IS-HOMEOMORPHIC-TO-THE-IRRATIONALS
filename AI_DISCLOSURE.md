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
5. The author asked for a complete Lean formalization of Theorem A, including the classical results it uses, and for a further review of the proofs. The formalization is described below; the review led to a shorter proof of Lemma 3.5(c) and to one added sentence in Section 6.1.

ChatGPT-Astra (OpenAI) was used, together with the author, to check successive versions of the manuscript and to send feedback.

Claude formalized the complete proof of Theorem A in Lean 4 (version 4.35.0) with Mathlib (commit `6015dbb`), including the classical results it uses. The Lean source accompanies this paper as supplementary material; it builds with `lake build`, and `lake env lean CheckAxioms.lean` lists the axioms used. The development contains no `sorry`, adds no axioms and has no hypotheses; it uses only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. Its final theorem states that there is a compact connected set $X\subseteq\ell^2$ with more than one point such that $\mathcal D(X)$ is homeomorphic to $\mathbb N^{\mathbb N}$ and to $\mathbb I$. The formalization covers:

- the template continuum, Fact 2.4(a),(d) for it, and Lemma 3.1; points in distinct composants are formalized as points not lying in a common proper subcontinuum, which makes Fact 2.4(c) immediate, and Lemma 3.1 is proved with the Baire category theorem;
- the realization in $\ell^2$, Lemma 3.2, Lemma 3.3(a)–(g) and the first assertion of (h), and Lemma 3.5(a),(c);
- the branch decomposition of Lemma 4.2, in an equivalent form with closed sides, Lemmas 4.3–4.5, and both directions of Theorem 4.6;
- Lemma 5.1 and Propositions 5.2 and 5.3;
- Proposition 5.4 in the form needed for Theorem A: every compact subset of the code space $\mathfrak D$ has empty interior, which transfers to $\mathcal D(X)$ through $\Phi$;
- Fact 2.5(a) in the direction used, the Alexandrov–Urysohn theorem (Fact 2.5(b)), proved with a Lusin scheme, and the homeomorphism $\mathbb N^{\mathbb N}\cong\mathbb I$ (Fact 2.5(c)).

The formalization differs from the text in presentation, not in substance:

- The template is the inverse limit of the tent map $t\mapsto\min(2t,2-2t)$ on $[0,1]$, a standard model of the Knaster continuum, viewed as a subset of $[0,1]^{\mathbb N}$. It is embedded in $\ell^2$ by $(z_n)\mapsto(2^{-(n+1)}z_n)$, and each piece receives its own infinite block of coordinates of $\ell^2$ instead of a plane. The proof uses planarity of $K$ only to fit each piece into a plane, so with infinite coordinate blocks any nondegenerate indecomposable continuum would serve as the template.
- The root offset $o_{B_\emptyset}$ is $\rho$ rather than $(0,0)$, and indices start at $0$; the scales are those of Section 3.2 after this relabelling.
- Condition (c) of Theorem 4.6 is encoded without geometry: for a countable base $(V_j)$ of $K$, put $N_j=\\{k:a_k\in V_j\\}$; an included spine $S_{\beta,m}$ must have, for every $j$, infinitely many included children $B_{\beta^\frown(m,k)}$ with $k\in N_j$. Lean proves that this is equivalent to (c).
- Proposition 5.4 is proved in the code space, by the code modifications of its two cases; Lemma 3.5(b) and the limit continua $A^\*$ are not needed.

The file `SanityChecks.lean` checks the translation on examples, and the development was also checked with the kernel replay tool `leanchecker` and with the independent type checker `nanoda`.

No independent expert has yet verified the proofs. The author takes full responsibility for the content.

---

**References cited above** (numbered as in the paper)

[1] J. Camargo, N. Ordoñez, and D. Ramírez, *On the hyperspaces of meager and regular continua*, Appl. Gen. Topol. **25** (2024), no. 2, 385–406. [doi:10.4995/agt.2024.20116](https://doi.org/10.4995/agt.2024.20116).

[8] D. A. Ramírez Angarita, *Los hiperespacios de subcontinuos regulares y subcontinuos magros*, undergraduate thesis, Universidad Industrial de Santander, Bucaramanga, 2023. Available at <https://noesis.uis.edu.co/entities/publication/cd4f0fe6-ec75-47d8-8e0a-617149375321>.
