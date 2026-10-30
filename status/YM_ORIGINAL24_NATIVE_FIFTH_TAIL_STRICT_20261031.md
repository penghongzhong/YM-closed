# YM-closed Original24: fixed-U1 native shell → true Schwartz B10 → all-RG-scale tail (strict LEAP receipt)

Date: 2026-10-31.
Repository: penghongzhong/YM-closed
Branch: ym-original24-source-tail-native-20261031
Source: YMOriginal/Original24_TrueSchwartzScaleTail.lean
Source commit: a3136e0acc61f71c0e04add9fc2fd085dabdbcef.
Official Lean 4.35.0-rc3; Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.
**GitHub Actions #41135883914 SUCCESS.** 9011/9011 actual Lake tasks; \`-DwarningAsError=true\` replay; full \`#print\` of exact terminal and \`#print axioms\` successful.
Only [propext, Classical.choice, Quot.sound]. No sorry, admit, sorryAx, custom axiom.
https://github.com/penghongzhong/YM-closed/actions/runs/41135883914

## Newly completed IN ONE MAIN-CHAIN terminal declaration

\`YMUIC.Original24.original24_real_connected_schwartz_postR_all_scales\` uses:
1. SAME exact U1Data old/new-R fields, RG index j and background omega;
2. actual finite SU(2) periodic lattice holonomy Wilson roots and original bounded Wilson-word coefficient budgets;
3. **physical per-block integer native-shell count**:
   # {X through Delta : d X = m} <= Cpol exp(cpol m),
   with \`kappaR - kappa - cpol > 0\`;
   \`hcount\` is NO LONGER an independent theorem assumption, but derived from
   \`actual_native_U1_shell_count_to_block_norm\` as
   sum_{X through Delta} exp(-(kappaR-kappa)d X)
      <= Cpol/[1-exp(-(kappaR-kappa-cpol))].
4. actual 4D Schwartz test f and its true fifth derivative; NO hB10 remainder theorem hypothesis, NO post-R tail bound or summability hypothesis;
5. previous U1 / U2 / FP tree-rooted source coefficient bounds as **explicit still unproved physical/model analysis interfaces**.
6. geometric RG scale a_j/a_n = L^{-m}, four-dimensional placement and theta-norm loss, with L>1, 0<theta<1.

Terminal derived estimate for each truncation and each m:
||rem_m|| <= M * [L^{-(1-theta)}]^m;
Summable(||rem_m||);
sum_m ||rem_m|| <= M / [1-L^{-(1-theta)}].
Here M = 5 K Croot Mf (Aold+Anew) / mu^5, and Aold/Anew are the actual U1 old/new activity prefactors TIMES shell-derived Ccount.

This is genuinely derived fifth-order Schwartz Taylor and sum; NOT a repackaged hB10 input. This DOES NOT YET assert that the actual renormalized Bałaban R-operation post-source coefficients are precisely the finite Mayer coefficients.

## Full original manuscript environment 24: still open (historical union 37/39 = 94.87%)

Original24 is C29 theorem 15.5 \`thm:B11-repair\` with fixed-D physical \`C-LOCAL-POLY-LF_D=CLOSED\`. Completing it needs:
- All-n physical extended-two-root Penrose/Fernández–Procacci *weighted labeled-tree-to-exponential finite-height enumeration*, currently \`PhysicalExactTwoRootFPCriterion\` still an EXPLICIT unproved premise. The single-q graph embedding/tree transport/card bound/weighted bound and n=1 coefficient are strictly verified; they do NOT establish all orders.
- Actual native CMP119/CMP122 Balaban R-history -> finite hard-core polymer U1Data / activities / source adjacency / distances, uniformly in cutoff, volume, RG step, background. Current shell geometry \`hShell\` is an explicit original published/model input, not derived from full CMP histories.
- Actual canonical source jet and engineering a^(4-d) normalization, physical sourceLift and extraction/inclusion maps, fifth-order post-R norm and B09 finite-dimensional counterterm mixing identification on the **same physical source**.
- Source-specific positive weak window (kappa0>0 and p0(g)->infinity) strictly implies both quantitative margins in independent Actions #41133232384; that extra analytical asymptotic is not yet part of published U1Data and its real CMP instance is unverified.

The separately verified fixed-D convergence/cocycle term \`original24_fixedD_same_source_full_series_and_cocycle\`, Actions #41123878633, uses explicit published FP and an arbitrary scalar \`sourceLift\`; it has not been combined with the actual above Schwartz fifth tail for the exact native source. **Do not count it as 38/39.**

Original30 true renormalized all-order joint Schwartz E0' and I7 gap remain open; no unconditional mass-gap claim.

## Next shortest chain

Prove the genuine all-n Fernández–Procacci exponential enumeration in Lean, preferably for the fixed-q doubled-fugacity source, then use it to discharge hFPold/hFPnew in a version of this theorem. Establish native CMP R-history and actual canonical jets; only then compile the meaningful unchanged Original24 terminal and register 38/39. Default main unchanged.
