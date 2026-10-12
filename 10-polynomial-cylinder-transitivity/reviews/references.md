# Literature and scope

Checked on October 12, 2026. These references distinguish the main cancellation question from the scoped symmetry theorem proved here.

## Cancellation

The affine-space formulation asks whether A[w] ≅ k[x₁,…,xₙ₊₁], for an affine k-algebra A, implies A ≅ k[x₁,…,xₙ]. It is distinct from cancellation between arbitrary affine varieties, which already has characteristic-zero counterexamples.

- Abhyankar, Eakin and Heinzer, *On the uniqueness of the coefficient ring in a polynomial ring*, J. Algebra 23 (1972), 310–342. The dimension-one case is classical. https://doi.org/10.1016/0021-8693(72)90134-2
- Crachiola and Makar-Limanov, *An algebraic proof of a cancellation theorem for surfaces*, J. Algebra 320 (2008), 3113–3119. This gives an algebraic proof of affine-plane cancellation over algebraically closed fields. The theorem is now known over arbitrary fields; see the historical summary in Gupta's ICM survey. https://www.sciencedirect.com/science/article/pii/S0021869308004146
- Neena Gupta, *On Zariski's Cancellation Problem in positive characteristic*, Adv. Math. 264 (2014), 296–307. Affine-space cancellation fails in every dimension n≥3 in positive characteristic. https://arxiv.org/abs/1309.1368
- Neena Gupta, *The Zariski Cancellation Problem and related problems in Affine Algebraic Geometry*, ICM proceedings. This explains the classical known/open boundary and characteristic-zero candidate threefolds. https://arxiv.org/abs/2208.14736
- Ghosh, Gupta and Pal, *On the family of affine threefolds a(x)y=F(x,z,t)*, J. Algebra 700 (2026), 267–288. The stable-polynomial equivalent conditions in its characteristic-zero theorem retain Makar-Limanov or Derksen invariant hypotheses. It is not unconditional cancellation for all such threefolds. https://doi.org/10.1016/j.jalgebra.2026.04.008 ; accessible author preprint: https://arxiv.org/html/2403.17397v2

Recent OpenAI/math repository material claims a dimension-four complex counterexample and related stable-coordinate results. The primary scope and main proof files were read, but those external formalizations were not independently rebuilt or validated in this project. They must not be treated here as verified results. Their stated dimension-four example does not settle dimension-three cancellation. Primary scope: https://raw.githubusercontent.com/openai/math/main/lean/docs/047.md ; main file: https://raw.githubusercontent.com/openai/math/main/lean/OAI/Algebra/AffineCancellation/Main.lean . No result in this package settles dimension-three cancellation.

## Closest antecedent and the scoped extension

- Pierre-Marie Poloni, *The cylinder over the Russell cubic threefold is flexible*, arXiv:2609.14090v1, September 12, 2026. Theorem 1.4 states the four-action transitivity result for P(t)=t³. The adapted embedding, auxiliary expressions a,c,m, and the cubic infinitesimal generator are directly attributed to this paper. https://arxiv.org/html/2609.14090
- Arzhantsev, Flenner, Kaliman, Kutzschebauch and Zaidenberg, *Flexible varieties and automorphism groups*, Duke Math. J. 162 (2013), 767–823. Theorem 0.1 supplies the geometric flexibility and infinite-transitivity corollary. It is cited rather than formalized in this package. https://doi.org/10.1215/00127094-2080132
- Gaifullin and Petrov, *Non-cancellative varieties, maximal tori, and the Makar-Limanov invariant*, arXiv:2607.13593. Nearby results concern generic flexibility and local-slice constructions. https://arxiv.org/html/2607.13593
- Isaev, *The flexibility of m-suspensions constructed via a local slice*, arXiv:2607.11678. Its suspension equations do not directly have the extra linear-x term in this family. https://arxiv.org/html/2607.11678v1

The extension derived here permits every nonconstant P and supplies a uniform 13-move bound with explicit polynomial actions. The targeted search found no primary source stating that full extension. This supports a carefully attributed scoped contribution, not a claim of exhaustive novelty certification or priority.
