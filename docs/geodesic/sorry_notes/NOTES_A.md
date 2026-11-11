
## FlowInterface.lean (Chapter A) — wave 2 status

All `sorry`s in `KolmogorovMathlib/PointToSet/Geodesic/FlowInterface.lean` are now filled
(`lake env lean` reports zero errors and no `sorry` warnings).

### Changes to the file header
- Added `import KolmogorovMathlib.Oracle.KraftChaitin` (needed for `oracle_kraftChaitin_bound`;
  the module was not in the import closure). No other import or statement was changed.

### New lemma (Task 1), exactly as requested
`theorem oracleNatComplexity_le_log_add_loglog (A : Set ℕ) : ∃ c : ℝ, ∀ n : ℕ,
  (oracleNatComplexity A n : ℝ) ≤ Real.logb 2 (n + 1) + 2 * Real.logb 2 (Real.logb 2 (n + 1) + 1) + c`
(section `natComplexity`, right after section `orbitComplexityNat`). Proof: Kraft–Chaitin on the
request stream `n ↦ (natBits n, |bits n| + 2 |bits |bits n|| + 3)` (mass ≤ 1/4 via the private
regrouping lemma `tsum_inv_two_pow_size_mul_le`), then `length_bits_le_logb_add_one` twice;
the constant is `c_KC + 8`.

### New public lemmas (Task 2), in section `orbitNames` (before `geo:orbit-extension`)
- `isComputableRealFamilyIn_dist_iterate_ideal (P T A) (hP) (hTA) :
    IsComputableRealFamilyIn A fun d : ℕ × ℕ × ℕ ↦ dist (T^[d.1] (P.ι d.2.1)) (P.ι d.2.2)`.
  Built from a local copy (private, same names) of the library's private orbit-name lemmas
  `exists_constant_oracle_indices`, `exists_oracle_specialization`, `exists_iterate_indices`,
  `isCauchyName_of_iterate_indices`, `computable_names_of_total_oracle_indices`,
  `exists_computable_orbit_names` (`BirkhoffComputability.lean` lines 46–266) and a local copy of
  Chapter C's `isComputableRealFamilyIn_dist_names`. If those become public in the library, the
  copies can be deleted.
- `IsREIn.list_forall_get {F : α × ℕ × β → Prop} (hF : IsREIn A F) :
    IsREIn A fun d : α × List β ↦ ∀ k (h : k < d.2.length), F (d.1, k, d.2.get ⟨k, h⟩)`
  (position-indexed bounded ∀; certificate = enumeration stage, checked by `Nat.rec`).
- `isREIn_mem_bowenBall_inter_pullbacks` is proved from these (order `0` handled by mapping the
  radius to `1`, since `bowenDist T 0 = 0` while the order-zero ball is `univ`).

### `orbit_extension` (Task 3), proved with the statement's constants (`ε : ℚ`)
No variant needed. Construction: net `l := s.toList` from `exists_finite_ideal_net`, `N := l.length`.
If `N ≤ 1` the space has diameter `< ε` and the `K(n, ε)` realizer already works (`c := 0`).
If `N ≥ 2`: itinerary numeral `J := Nat.ofDigits N (D ++ [1])` with `D` the net indices along
`T^[n+k] y`, `k < m` (so `N^m ≤ J`, `J + 1 ≤ 2 N^m`, and `m` is recovered as the number of digits);
decoder (private `exists_extension_decoder`) = `rfindOpt` over an enumeration of the semidecidable
predicate `(digit-count check) ∧ isREIn_mem_bowenBall_inter_pullbacks`; complexity via
`oracle_tuple_bounds_composition` with `k = 2` on `[pairCode (natBits i) (natBits n), natBits J]`,
`oracle_tuple_bounds_overhead` for the pair, and `oracleNatComplexity_le_log_add_loglog` for `J`
(`log₂(J+1) ≤ 1 + m ⌈log₂ N⌉`, `2 log₂(log₂(J+1)+1) ≤ 2 log₂(m+1) + 2 log₂(⌈log₂ N⌉+2)`).
Constant: `c := ⌈c₁ + c₂ + c₃ + 1 + 2 log₂(⌈log₂ N⌉ + 2)⌉₊`.
