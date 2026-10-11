# Complexity and probability audit

The fully specified candidate investigated was a single rational coordinate f of degree D and a fixed rational recurrence R of degree r on translation by G. The hypothesis D(r+1) < n with full coverage is refuted by the manuscript's analytic proof. There is no remaining algorithm with a claimed improvement to audit as though it existed.

## Exact baseline

For m = ceil(sqrt(n)), BSGS builds the m points jG and tests Q - imG for 0 <= i < m. The decomposition d = im+j guarantees a match. Each returned scalar is range-checked and verified by multiplication. On valid subgroup inputs the answer is unique and the success probability is one.

The primary implementation rebuilds the baby table for each target. Its group-operation count is O(sqrt(n) + log(n)), including final verification; storage is O(sqrt(n)) points. Dictionary operations use expected lookup costs. A deterministic sorted-table variant adds comparison overhead without changing the group-operation exponent.

The 763 test targets are all points on the 13 generated curves. They are not a sample with an estimated probability of solver correctness.

## Equivalent models

A group addition is not a bit operation. With B = ceil(log2(p)), field multiplication cost M(B), and inversion cost I(B), affine arithmetic gives an arithmetic bound O((sqrt(n)+log(n))*(M(B)+I(B))) for this baseline. Equality, lookup, and memory are charged separately. Mathematical table contents need O(sqrt(n)*(B+log(n))) bits, with Python object overhead in addition.

Extension fields need their actual coefficient representation and arithmetic costs. An operation in F_(q^k) cannot be treated as a unit-cost F_q operation while k grows.

Pollard rho is an established low-memory generic comparison, not the implemented solver here. Its customary expected square-root work uses the appropriate pseudorandom-walk assumptions. Shoup's generic lower bound concerns random encodings and uniform secrets, with generic oracle work accounted for; it is not a lower bound for arbitrary coordinate-exploiting algorithms or free unlimited preprocessing. Primary references are listed in PRIOR_ART.md and the manuscript.

## Precomputation and amortization

For a hypothetical reduction, record setup time S, setup memory M_S, evaluation cost C_f, target orbit-index inversion C_inv, and verification C_ver. Single-target time includes S+C_f+C_inv+C_ver. An amortized claim must specify how many targets share which data. A precomputed full logarithm table cannot be hidden inside f.

The exhaustive point counts, complete orbits, PGL enumeration, and tiny set-cover dynamic program are research verification costs, not efficient preprocessing for a proposed cryptographic algorithm. Their generalization to large fields would be expensive.

## Degree is not running time

The exact morphism f_t = x composed with [2^t] has degree 2*4^t in characteristic different from two, yet it is evaluated using t doublings. The executed t=8 control has algebraic degree 131072 and uses eight doublings. The degree is a property of the morphism; a different morphism can agree with it on a finite group.

Therefore the proven D >= n/2 necessary condition for a full Mobius recurrence does not imply a square-root or linear time lower bound. A dense expansion would be a different, explicitly restricted representation model. No sparse or circuit lower bound is supplied.

## Distributions and adaptive choices

The deterministic agreement theorem needs no distribution. To obtain an agreement probability, P is uniform on H and f and the recurrence menu are fixed before P is drawn. Public-parameter dependence is allowed. Choosing f or a new R after observing the target requires a separate family or adaptive analysis.

The finite menu may select any available branch per point. This makes the mathematical upper bound stronger, but does not supply an efficient selector. Correctly predicting f(P+G) is not the same event as recovering d.

The experiment curves are selected lexicographically, not uniformly. Six predetermined coordinates are used. Rational-map coefficient samples use a fixed pseudorandom seed and rejection to ensure actual degree and coprimality. No random-curve or large-parameter success extrapolation is made. Runtime measurements in JSON are diagnostic only.

## Scope left open

Multiple coordinates, general algebraic correspondences, history-dependent states, high-degree compact circuits, adaptive families, and other non-generic ECDLP methods are not excluded. The necessary extension degree is not a sufficient construction or a runtime estimate. No faster algorithm and no general classical ECDLP security proof are claimed.
