# Independent semantic review of the paper

Date: 2026-10-09. Reviewed `short-private-pools.tex`, 436 lines, SHA-256 `b87be43a2f8a5e5c09ce9950db88029e09ca8afb034827068ca7fe40f641f848`, against the independently reviewed V2 Lean semantics. Locations below refer to that version. This is mathematical/source review; PDF visual QA and the separate clean-build audit are not repeated here. No author source was edited.

## Verdict

The central finite compiler theorem, its proof strategy, operational refinement, and initialization-inclusive multiplication accounting match the audited V2 model. The paper preserves the important restrictions: deterministic maximum epoch allowance; locally fixed candidates; committed final threshold; independent finite rational tapes; separate source-security assumption; exact divisibility; atomic serialized execution; explicit sampling/reset bursts; and field-coordinate rather than total-memory accounting.

**Revise the specific statements below before finalizing.** The principal presentation issue is the comparison's omission of the pool's additive error when calling the displayed levels exact confidence targets. There is also one false intermediate sentence in the mixed-output proof, readily repaired by retaining the invalid-event gate. Neither issue invalidates the stated main theorem or the Lean endpoint.

## Required corrections

### 1. Retain the pool's additive error in the comparison

Locations: line 314; table heading and pool row, lines 330–338. Also consider the abstract's wording at line 44.

The checked bound at deterministic T=t is `Pr[IA] <= 2^(-t) + Emax*delta`. It does not prove `Pr[IA] <= 2^(-t)` at exactly t checks. The table currently calls `1-2^(-b)` a “Target confidence” and assigns the pool b checks, alongside RS thresholds with exact error at most `2^(-b)`. The paragraph says the pool “reaches” those confidence levels without mentioning the additive term.

Minimal accurate repair:

- Rename the heading “Nominal progressive confidence alpha(b)=1-2^(-b).”
- Add immediately below the table: “The pool's aggregate error at a fixed displayed depth b is bounded by 2^(-b)+Emax*delta, with Emax*delta<2^(-222) at the stated allowance. The RS entries bound error by 2^(-b) without that pool term. The table compares nominal confidence levels with this explicit slack; it does not equate their exact finite error bounds.”
- At line 314 say “returns its first six nominal confidence levels, with the additive error in Theorem ...” instead of unqualified exact target attainment.

An alternative is to compare a common relaxed target `2^(-b)+2^(-222)`, but then justify the displayed RS minimality thresholds for that relaxed target. Do not silently drop the additive error or assert that negligibility makes the two finite bounds equal. The multiplication inequality itself is unaffected.

### 2. Keep the mixed-output gate in the soundness proof

Location: line 209.

“Outside Bad, the selected final residual has K<=u-1 zero rows” is false for ordinary-valid output branches: their actual residual is zero and K=s. A repaired dummy may have few zero rows, but it is not the actual residual on such a branch. The Lean event gate handles this correctly.

Replace the first two sentences with:

“Outside Bad, on a branch eligible for IA, the selected nonzero residual has K<=u-1 zero rows. On all other branches the conditional probability of IA is zero. Consequently, conditional on the complete pre-final state, the probability of IA outside Bad is at most rho^T.”

The subsequent displayed sums then follow exactly as written. At line 207, “incoming observable history” would also be clearer than the unqualified “history”: the hidden prefetched bank is not part of the conditioning information in the freshness argument.

### 3. Qualify the informal parameter-regime necessity

Location: line 358.

The exact preparation share is `W/d = snm/[R(m+n)]`. For unrestricted dimensions, R much larger than sn is sufficient, but not necessary: when m is much smaller than n, the relevant scale is approximately sm instead. The paper's general model does not assume m>=n.

Either write:

“In the regime m>=n, including our example, a small preparation share requires R large relative to sn; together with Rk+s<q, this motivates a modulus appreciably larger than skn.”

or describe R much larger than sn as a sufficient regime and display the exact share. Avoid an unqualified necessity claim for arbitrary dimensions.

### 4. State the sampling range for the RS ratio

Location: lines 321–325.

The without-replacement experiment and denominator require `0<=t<=1154`. Add that range. For t>1023 within this range the numerator is zero, as expected. The six displayed thresholds are all within range and their arithmetic is consistent with the artifact.

## Recommended clarity/completeness edits

- **Public acceptance rule, line 115:** say “If Aux(x) holds and all projected checks pass, the interface returns alpha(T); otherwise it rejects.” The current first sentence mentions only projected checks, though the surrounding text and theorem correctly preserve Aux.
- **Compiler theorem hypotheses, lines 193–202:** restate `1<=u<=s`, `rho=(u-1)/s`, and the definition of delta in the theorem statement, rather than making a reader retrieve them from earlier sections. Positive s and 0<=rho<1 are important for the confidence interpretation.
- **Finite maximum allowance, lines 84 and 267:** the text already correctly distinguishes Emax from the reached epoch count. A concrete formula such as `Emax=floor(Q/R)+1` for a Q-prior-invocation budget would make the lifetime accounting self-contained. Use a conservative allowance consistent with whether Q includes the final call.
- **Terminal coupling, lines 304–306:** its bound is mathematically reasonable for the declared atomic full-block interface. For a “complete proof” presentation, explicitly fix the external tape, follow the ideal verifier that accepts valid equations and rejects invalid ones, and union-bound the at-most-Q+1 nonzero residuals along that ideal path. Each has unconditioned all-seven probability q^-7. This avoids accidentally suggesting that the real key remains uniform after conditioning on previous rejections. Valid and Aux-failing inputs reveal only key-independent results on that path.
- **Addition accounting, lines 260–263:** the paper's addition formula follows from one accumulator addition per preparation step plus the checked stored-dot counts. The preparation state instruments multiplications, not a separate global addition counter. It is fine to give the direct mathematical addition count, but avoid implying a separately named Lean total-addition-counter theorem exists unless adding one.
- **Build numbers, lines 57 and 406:** the 862 theorem declarations and peak RSS belong to the separate rebuild report, not this review. Keep them only if that report confirms those exact values for the same frozen manifest. The source manifest quoted in the paper matches the audited V2 manifest.

## Substantive statements checked and accepted

- Stored-row identity, perfect completeness, alpha monotonicity/nontriviality, and threshold clamping.
- Adaptive transcript-cell factorization without assuming independence of query choices.
- Unspoiled-row excluded-kernel count and the conservative q−L−s denominator.
- Adaptive first-spoil tail by fixed-position product bounds and a union bound.
- Frozen virtual final pass and distinct first-spoil charging.
- State-dependent threshold sampling and the separate joint-threshold sum; no illicit conditional-on-rare-T claim.
- Maximum-epoch union bound and finite independent-tape averaging.
- Separation of original-valid forgeries from additional verification errors without claiming an EUF reduction.
- Actual matrix preparation/promotion, final reserved call, trace-free refinement, and exact multiplication formula B+NW+dS.
- Explicit sn-sample promotion bursts and disclosed dense-array zero-fill writes. The latter are implementation accounting, correctly not represented as a Lean machine-code theorem.
- Inventory nm+2s(n+m) with its exclusions, and exact finite parameter arithmetic.
- Narrow initialized-work crossing against the seven-row block, subject to the confidence-slack correction above; no runtime or whole-resource dominance.

Prior-work attribution and originality claims require the separate literature review; this audit does not independently re-open every cited primary source. The paper's stated modest combined-method contribution does not exceed the semantic scope of the V2 theorem. Once the required corrections are made, I see no remaining mathematical mismatch with that scope.

## Final revised-source disposition — PASS

Final review: 2026-10-09. Reviewed revised `short-private-pools.tex`, SHA-256 `b305c71785d72c8d91d585e738e9d9ba0cbe1e4570e19573c1fb7d0b1d608d33`.

**PASS.** The four required corrections above are resolved: the comparison explicitly retains nominal confidence and additive slack; the good-event proof retains the invalid-acceptance gate; the parameter-regime claim is qualified by the dimensions; and the RS sampling range is stated. The compiler theorem now restates its threshold parameters, the public rule explicitly preserves Aux, and the epoch allowance and terminal first-error coupling are explained.

The newly added three-row terminal comparison was checked with exact integer arithmetic: `(2^64+1)*2^25 < 1073741789^3`, whereas `(2^64+1)*2^26 < 1073741789^3` is false. The stated first-two-checkpoint comparison follows from `2W<d` with the disclosed initialized average-work interpretation. No new mathematical error was found in the revised source.

The earlier findings remain above as review history, not outstanding required edits. This final PASS concerns mathematical semantics and correspondence with audited V2 scope; separate PDF visual QA, literature review, and clean-build reports retain their own scopes. No underlying author source was changed by this reviewer.
