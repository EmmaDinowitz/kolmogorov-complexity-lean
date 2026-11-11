# Part 1, second half of Surface/Riccati.lean (rates, Sing, transversality)

Copy: /home/user/part1_worker2/Riccati.lean. Status: every sorry from the section
"The rates `lamU` and `lamS`" to the end is filled; 0 errors, 31 sorry warnings (all in the
first half, untouched). No statement believed false.

Header: the copy needs `import Mathlib.Analysis.ODE.ExistUnique` (same line the repository file
already has) for HasDerivAt.mul/div/exp, MeanValue monotonicity lemmas, IsLocalMin.

| group | theorems | proof idea |
|---|---|---|
| reversal | lamS_eq_reverse_lamU, all lamS lemmas | `logDerivTo_eq_reverse` inside the iInf; lamS facts = reverse.lamU facts |
| limits/bounds | tendsto_logDerivFrom_lamU, lamU_le_logDerivFrom, lamU_nonneg, lamU_le | ciInf_le / le_ciInf (bdd below by 0), antitone via logDerivFrom_mono_pole, `tendsto_order`; lamU_le by limit of `1/T + Λ` |
| unstable solution | exists_unstable_jacobiSolution (helper aux2_unstable) | basis a,b at 0; jacobiFrom v (-S) = J(0)(a + c_S b) by uniqueness, c_S -> lamU; y = a + lamU b is a pointwise limit of positive functions, >0 by min/double-zero argument; y'/y = lim logDerivFrom v (-S) t = lamU(φ t v) (logDerivFrom_flow); y' = lamU(φ t v) y >= 0 so y <= 1 on t <= 0 |
| Riccati along orbit | hasDerivAt_lamU_flow, hasDerivAt_lamS_flow | lamU∘φ = y'/y, quotient rule; lamS via reverse and composition with negation |
| uniqueness (bounded) | deriv_div_eq_lamU_of_bounded | if y'(0) != lamU y(0), jacobiTo v 0 = α w + β y (w unstable) is bounded on t <= 0, but jacobiTo v 0 t >= -t |
| uniqueness (Riccati) | eq_lamU_of_riccati_nonneg | Y global solution with Y(0)=1, Y'(0)=u(0); g = Y' - uY has g' = -ug, g(0)=0, so g = 0 on t<=0 (Grönwall by hand: g^2 e^{2Bs} monotone on [t,0]); then Y>0 (IVT + double zero), Y<=1 (Y' = uY >= 0), apply previous theorem. tanh-type solutions are excluded by hnn, statement is correct |
| continuity | continuous_lamU, continuous_lamS | no Dini needed: Wronskian of w and J = jacobiFrom v (-T) gives logDerivFrom v (-T) 0 - lamU v = w(-T)/J(0) <= 1/T uniformly in v (J(0) >= T); uniform limit of continuous functions |
| Sing | lamU_eq_zero_iff, lamS_eq_zero_iff, mem_Sing_iff, isClosed_Sing, invariance, Sing_eq_univ_iff, Reg_nonempty | lamU=0 => w' monotone, >= 0, w'(0)=0 so w'=0 on t<=0, each such t is a min of w' so K w = 0; converse: u = 0 in eq_lamU_of_riccati_nonneg; invariance from orbitK_flow |
| transversality | lamU_add_lamS_pos_iff, lamU_pos_or_lamS_pos_of_mem_Reg | nonnegativity + definition of Reg |
