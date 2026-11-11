/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.PrefixComplexity.Information

/-!
# Located families of names

The split-precision theory of mutual information concerns objects (points of a metric space,
tuples of points) that are known only through *names*: strings ranging over a set `S` (the
codes of the rational points of a ball, the codes of tuples of such points).  Everything the
theory uses about such a set is captured by a `LocatedFamily`: a family `names r` of nonempty
sets of strings indexed by precisions `r : ι`, a budget `budget r : ℕ` (the `O(log r)` of the
notes), and two properties up to constant multiples of `budget r + 1`:

* **transfer**: every name of `names r` describes every `K`-minimizer of `names r`
  (`K(p | q) ≤ O(budget r)`), the one-sided fact behind the transfer lemmas of the notes; and
* **growth**: the complexity of a minimizer has `O(budget r)` bits.

From these the derived transfer lemmas follow: a minimizer may replace a name in the condition
(`LocatedFamily.transfer_cond`), also in the presence of the complexity value
(`LocatedFamily.transfer_context`, the decorated transfer lemma), and names are no simpler than
minimizers.  The product of two located families is a located family on the product index with
the sum of the budgets (`LocatedFamily.prod`, requiring the lower direction of symmetry of
information); this is the coordinatewise iteration of the notes together with the comparison
of joint and marginal minimizers.

Blueprint nodes `split:located`, `split:transfer`, `split:product`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

/-- Combining per-precision budgets into one multiple of the total budget. -/
theorem budget_combine (c₁ c₂ k b₁ b₂ : ℕ) :
    c₁ * (b₁ + 1) + c₂ * (b₂ + 1) + k ≤ (c₁ + c₂ + k) * (b₁ + b₂ + 1) := by
  nlinarith

/-- The binary length of a sum is at most the sum of the binary lengths plus one. -/
theorem bits_length_add_le (a b : ℕ) :
    (Nat.bits (a + b)).length ≤ (Nat.bits a).length + (Nat.bits b).length + 1 := by
  simp only [Nat.size_eq_bits_len]
  rw [Nat.size_le]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 2 ^ a.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ b.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

variable (A : Set ℕ)

/-! ### Minimizers of a set of names -/

/-- `p` is a `K^A`-minimizer of the set of names `S`. Blueprint node `split:located`. -/
def IsMinName (S : Set BitString) (p : BitString) : Prop :=
  p ∈ S ∧ ∀ q ∈ S, oracleComplexity A p ≤ oracleComplexity A q

/-- The least complexity of a name in `S` (zero on the empty set).
Blueprint node `split:located`. -/
noncomputable def minComplexity (S : Set BitString) : ℕ :=
  sInf (oracleComplexity A '' S)

/-- A nonempty set of names has a minimizer. Blueprint node `split:located`. -/
theorem exists_isMinName {S : Set BitString} (hS : S.Nonempty) : ∃ p, IsMinName A S p := by
  obtain ⟨q₀, hq₀⟩ := hS
  have hne : (oracleComplexity A '' S).Nonempty := ⟨_, q₀, hq₀, rfl⟩
  obtain ⟨p, hp, hpeq⟩ := Nat.sInf_mem hne
  refine ⟨p, hp, fun q hq => ?_⟩
  rw [hpeq]
  exact Nat.sInf_le ⟨q, hq, rfl⟩

/-- A minimizer attains the least complexity. Blueprint node `split:located`. -/
theorem IsMinName.minComplexity_eq {S : Set BitString} {p : BitString} (hp : IsMinName A S p) :
    minComplexity A S = oracleComplexity A p := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨p, hp.1, rfl⟩
  · refine le_csInf ⟨oracleComplexity A p, p, hp.1, rfl⟩ ?_
    rintro _ ⟨q, hq, rfl⟩
    exact hp.2 q hq

/-- The least complexity is at most the complexity of any name. Blueprint node
`split:located`. -/
theorem minComplexity_le {S : Set BitString} {q : BitString} (hq : q ∈ S) :
    minComplexity A S ≤ oracleComplexity A q :=
  Nat.sInf_le ⟨q, hq, rfl⟩

/-- Two minimizers have the same complexity. -/
theorem IsMinName.complexity_eq {S : Set BitString} {p p' : BitString}
    (hp : IsMinName A S p) (hp' : IsMinName A S p') :
    oracleComplexity A p = oracleComplexity A p' :=
  le_antisymm (hp.2 p' hp'.1) (hp'.2 p hp.1)

/-! ### Located families -/

/-- A family of sets of names indexed by precisions, with a budget controlling the transfer
between names and minimizers and the number of bits of the minimal complexity.
Blueprint node `split:located`. -/
structure LocatedFamily (ι : Type*) where
  /-- The names available at precision `r`. -/
  names : ι → Set BitString
  /-- There is always a name. -/
  nonempty : ∀ r, (names r).Nonempty
  /-- The error budget at precision `r`. -/
  budget : ι → ℕ
  /-- Every name describes every minimizer within the budget. -/
  transfer : ∃ c : ℕ, ∀ r, ∀ q ∈ names r, ∀ p, IsMinName A (names r) p →
    oraclePrefixComplexityNat A p q ≤ c * (budget r + 1)
  /-- The minimal complexity has at most a budget's worth of bits. -/
  bits_le : ∃ c : ℕ, ∀ r p, IsMinName A (names r) p →
    (Nat.bits (oracleComplexity A p)).length ≤ c * (budget r + 1)

namespace LocatedFamily

variable {A} {ι : Type*} (L : LocatedFamily A ι)

/-- The least complexity of a name at precision `r`. Blueprint node `split:located`. -/
noncomputable def complexity (r : ι) : ℕ := minComplexity A (L.names r)

/-- Every precision has a minimizer. -/
theorem exists_min (r : ι) : ∃ p, IsMinName A (L.names r) p :=
  exists_isMinName A (L.nonempty r)

/-- A minimizer attains `L.complexity r`. -/
theorem complexity_eq {r : ι} {p : BitString} (hp : IsMinName A (L.names r) p) :
    L.complexity r = oracleComplexity A p :=
  hp.minComplexity_eq

/-- Every name is at least as complex as `L.complexity r`. -/
theorem complexity_le {r : ι} {q : BitString} (hq : q ∈ L.names r) :
    L.complexity r ≤ oracleComplexity A q :=
  minComplexity_le A hq

/-! ### Derived transfer lemmas -/

/-- The unary code of a minimizer's complexity is within budget.
Blueprint node `split:transfer`. -/
theorem natCode_complexity_le :
    ∃ c : ℕ, ∀ r p, IsMinName A (L.names r) p →
      oracleComplexity A (natCode (oracleComplexity A p)) ≤ c * (L.budget r + 1) := by
  obtain ⟨c₁, hc₁⟩ := oracleComplexity_natCode_le A
  obtain ⟨c₂, hc₂⟩ := L.bits_le
  refine ⟨3 * c₂ + c₁, fun r p hp => ?_⟩
  have h1 := hc₁ (oracleComplexity A p)
  have h2 := hc₂ r p hp
  nlinarith

/-- **Transfer in the condition** (Lemma 3.1 of the notes): a name `q` may be replaced by a
minimizer `p` in the condition, with an arbitrary extra string `w` riding along:
`K(z | ⟨q, w⟩) ≤ K(z | ⟨p, w⟩) + O(budget r)`. Blueprint node `split:transfer`. -/
theorem transfer_cond :
    ∃ c : ℕ, ∀ r, ∀ q ∈ L.names r, ∀ p, IsMinName A (L.names r) p → ∀ z w : BitString,
      oraclePrefixComplexityNat A z (pairCode q w) ≤
        oraclePrefixComplexityNat A z (pairCode p w) + c * (L.budget r + 1) := by
  obtain ⟨c₀, hc₀⟩ := L.transfer
  obtain ⟨c₁, hc₁⟩ := oraclePrefixComplexityNat_triangle A
  obtain ⟨c₂, hc₂⟩ := oraclePrefixComplexityNat_pair_le_add A
  obtain ⟨c₃, hc₃⟩ := oraclePrefixComplexityNat_cond_pair_left_le A
  obtain ⟨c₄, hc₄⟩ := oraclePrefixComplexityNat_map_self_le A decodeSecond
    decodeSecond_computable.computableIn
  refine ⟨c₀ + c₁ + c₂ + c₃ + c₄, fun r q hq p hp z w => ?_⟩
  have h1 := hc₁ z (pairCode p w) (pairCode q w)
  have h2 := hc₂ p w (pairCode q w)
  have h3 := hc₃ p q w
  have h4 := hc₄ (pairCode q w)
  rw [decodeSecond_pairCode] at h4
  have h5 := hc₀ r q hq p hp
  nlinarith

/-- **Transfer in the condition, plain form**: `K(z | q) ≤ K(z | p) + O(budget r)`.
Blueprint node `split:transfer`. -/
theorem transfer_cond' :
    ∃ c : ℕ, ∀ r, ∀ q ∈ L.names r, ∀ p, IsMinName A (L.names r) p → ∀ z : BitString,
      oraclePrefixComplexityNat A z q ≤
        oraclePrefixComplexityNat A z p + c * (L.budget r + 1) := by
  obtain ⟨c₀, hc₀⟩ := L.transfer
  obtain ⟨c₁, hc₁⟩ := oraclePrefixComplexityNat_triangle A
  refine ⟨c₀ + c₁, fun r q hq p hp z => ?_⟩
  have h1 := hc₁ z p q
  have h2 := hc₀ r q hq p hp
  nlinarith

/-- **Decorated transfer** (Lemma 3.3 of the notes): the minimizer may also replace the name
when the condition carries the complexity value:
`K(z | ⟨q, K(q)⟩) ≤ K(z | ⟨p, K(p)⟩) + O(budget r)`. Blueprint node `split:transfer`. -/
theorem transfer_context :
    ∃ c : ℕ, ∀ r, ∀ q ∈ L.names r, ∀ p, IsMinName A (L.names r) p → ∀ z : BitString,
      oraclePrefixComplexityNat A z (prefixComplexityContext q (oracleComplexity A q)) ≤
        oraclePrefixComplexityNat A z (prefixComplexityContext p (oracleComplexity A p)) +
          c * (L.budget r + 1) := by
  obtain ⟨c₀, hc₀⟩ := L.transfer
  obtain ⟨c₁, hc₁⟩ := oraclePrefixComplexityNat_triangle A
  obtain ⟨c₂, hc₂⟩ := oraclePrefixComplexityNat_pair_le_add A
  obtain ⟨c₃, hc₃⟩ := oraclePrefixComplexityNat_cond_pair_left_le A
  obtain ⟨c₄, hc₄⟩ := oraclePrefixComplexityNat_le_oracleComplexity A
  obtain ⟨c₅, hc₅⟩ := L.natCode_complexity_le
  refine ⟨c₀ + c₁ + c₂ + c₃ + c₄ + c₅, fun r q hq p hp z => ?_⟩
  -- chain through the decorated minimizer
  have h1 := hc₁ z (prefixComplexityContext p (oracleComplexity A p))
    (prefixComplexityContext q (oracleComplexity A q))
  -- the decorated minimizer from the decorated name: the minimizer and its complexity value
  have h2 := hc₂ p (natCode (oracleComplexity A p))
    (prefixComplexityContext q (oracleComplexity A q))
  have h3 := hc₃ p q (natCode (oracleComplexity A q))
  have h4 := hc₄ (natCode (oracleComplexity A p))
    (prefixComplexityContext q (oracleComplexity A q))
  have h5 := hc₀ r q hq p hp
  have h6 := hc₅ r p hp
  rw [prefixComplexityContext_eq p, prefixComplexityContext_eq q] at *
  nlinarith

/-- A minimizer is simple given any name, and its complexity is at most that of the name:
the combined form used when the name is itself a minimizer of a larger family. -/
theorem complexity_le_of_mem {r : ι} {q : BitString} (hq : q ∈ L.names r) {p : BitString}
    (hp : IsMinName A (L.names r) p) : oracleComplexity A p ≤ oracleComplexity A q :=
  hp.2 q hq

/-! ### Products -/

/-- The product of two located families: names are pair codes of names, budgets add.
The transfer property of the product uses the lower direction of symmetry of information
to compare a joint minimizer with the pair of marginal minimizers.
Blueprint node `split:product`. -/
noncomputable def prod (hA : OracleSymmetryLower A) {ι₁ ι₂ : Type*}
    (L₁ : LocatedFamily A ι₁) (L₂ : LocatedFamily A ι₂) : LocatedFamily A (ι₁ × ι₂) where
  names rs := {w | ∃ q₁ ∈ L₁.names rs.1, ∃ q₂ ∈ L₂.names rs.2, w = pairCode q₁ q₂}
  nonempty rs := by
    obtain ⟨q₁, hq₁⟩ := L₁.nonempty rs.1
    obtain ⟨q₂, hq₂⟩ := L₂.nonempty rs.2
    exact ⟨pairCode q₁ q₂, q₁, hq₁, q₂, hq₂, rfl⟩
  budget rs := L₁.budget rs.1 + L₂.budget rs.2
  transfer := by
    obtain ⟨c₁, hc₁⟩ := L₁.transfer
    obtain ⟨c₂, hc₂⟩ := L₂.transfer
    obtain ⟨cT, hcT⟩ := oraclePrefixComplexityNat_triangle A
    obtain ⟨cP, hcP⟩ := oraclePrefixComplexityNat_pair_le_add A
    obtain ⟨cL, hcL⟩ := oraclePrefixComplexityNat_cond_pair_left_le A
    obtain ⟨cR, hcR⟩ := oraclePrefixComplexityNat_cond_pair_right_le A
    obtain ⟨cC, hcC⟩ := oraclePrefixComplexityNat_le_context_add A
    obtain ⟨cS, hcS⟩ := hA.bound
    obtain ⟨cW, hcW⟩ := oracleComplexity_pair_swap_le A
    obtain ⟨cU, hcU⟩ := oracleComplexity_pair_le_cond_context A
    obtain ⟨cX, hcX⟩ := oraclePrefixComplexityNat_context_le A
    obtain ⟨cN₁, hcN₁⟩ := L₁.natCode_complexity_le
    obtain ⟨cN₂, hcN₂⟩ := L₂.natCode_complexity_le
    obtain ⟨cNP, hcNP⟩ := oracleComplexity_natCode_le A
    obtain ⟨cB₁, hcB₁⟩ := L₁.bits_le
    obtain ⟨cB₂, hcB₂⟩ := L₂.bits_le
    obtain ⟨cA, hcA⟩ := oracleComplexity_pair_le_add A
    -- The constant: the per-coordinate coefficients and the accumulated additive constants.
    refine ⟨(2 * c₁ + 3 * cB₁) + (2 * c₂ + 3 * cB₂) +
      (2 * (cP + cL + cR) + (cS + cW + cU + cX) + 3 * (Nat.bits cA).length + 6 + cNP + cC + cT),
      ?_⟩
    rintro ⟨r, s⟩ q ⟨q₁, hq₁, q₂, hq₂, rfl⟩ p hp
    obtain ⟨p₁, hp₁⟩ := L₁.exists_min r
    obtain ⟨p₂, hp₂⟩ := L₂.exists_min s
    obtain ⟨u₁, hu₁, u₂, hu₂, hpu⟩ := hp.1
    -- `p = ⟨u₁, u₂⟩` is a joint minimizer; `p* = ⟨p₁, p₂⟩` the pair of marginal minimizers.
    have hmem : pairCode p₁ p₂ ∈
        {w | ∃ q₁ ∈ L₁.names r, ∃ q₂ ∈ L₂.names s, w = pairCode q₁ q₂} :=
      ⟨p₁, hp₁.1, p₂, hp₂.1, rfl⟩
    have hKp : oracleComplexity A p ≤ oracleComplexity A (pairCode p₁ p₂) := hp.2 _ hmem
    -- Step 1: `K(p* | q) ≤ K(p₁ | q₁) + K(p₂ | q₂) + O(1)`.
    have hs1 : oraclePrefixComplexityNat A (pairCode p₁ p₂) (pairCode q₁ q₂) ≤
        c₁ * (L₁.budget r + 1) + c₂ * (L₂.budget s + 1) + cP + cL + cR := by
      have a1 := hcP p₁ p₂ (pairCode q₁ q₂)
      have a2 := hcL p₁ q₁ q₂
      have a3 := hcR p₂ q₁ q₂
      have a4 := hc₁ r q₁ hq₁ p₁ hp₁
      have a5 := hc₂ s q₂ hq₂ p₂ hp₂
      omega
    -- Step 2: `K(p* | p) ≤ K(p₁ | u₁) + K(p₂ | u₂) + O(1)`.
    have hs2 : oraclePrefixComplexityNat A (pairCode p₁ p₂) p ≤
        c₁ * (L₁.budget r + 1) + c₂ * (L₂.budget s + 1) + cP + cL + cR := by
      subst hpu
      have a1 := hcP p₁ p₂ (pairCode u₁ u₂)
      have a2 := hcL p₁ u₁ u₂
      have a3 := hcR p₂ u₁ u₂
      have a4 := hc₁ r u₁ hu₁ p₁ hp₁
      have a5 := hc₂ s u₂ hu₂ p₂ hp₂
      omega
    -- Step 3: `K(p | p*, K(p*)) ≤ K(⟨p*, p⟩) - K(p*) + O(1) ≤ K(p* | p) + O(1)`.
    have hs3 : oraclePrefixComplexityNat A p
        (prefixComplexityContext (pairCode p₁ p₂) (oracleComplexity A (pairCode p₁ p₂))) ≤
          oraclePrefixComplexityNat A (pairCode p₁ p₂) p + cS + cW + cU + cX := by
      have a1 := hcS (pairCode p₁ p₂) p
      have a2 := hcW p (pairCode p₁ p₂)
      have a3 := hcU p (pairCode p₁ p₂)
      have a4 := hcX (pairCode p₁ p₂) p (oracleComplexity A p)
      omega
    -- Step 4: the complexity value of `p*` has `O(budget)` bits.
    have hs4 : oracleComplexity A (natCode (oracleComplexity A (pairCode p₁ p₂))) ≤
        3 * (cB₁ * (L₁.budget r + 1) + cB₂ * (L₂.budget s + 1)) +
          3 * (Nat.bits cA).length + 6 + cNP := by
      have a1 := hcNP (oracleComplexity A (pairCode p₁ p₂))
      have a2 := hcA p₁ p₂
      have a3 := hcB₁ r p₁ hp₁
      have a4 := hcB₂ s p₂ hp₂
      have hsize : (Nat.bits (oracleComplexity A (pairCode p₁ p₂))).length ≤
          (Nat.bits (oracleComplexity A p₁)).length +
            (Nat.bits (oracleComplexity A p₂)).length + (Nat.bits cA).length + 2 := by
        have hmono : (Nat.bits (oracleComplexity A (pairCode p₁ p₂))).length ≤
            (Nat.bits (oracleComplexity A p₁ + oracleComplexity A p₂ + cA)).length := by
          simp only [Nat.size_eq_bits_len]
          exact Nat.size_le_size a2
        have h1 := bits_length_add_le (oracleComplexity A p₁ + oracleComplexity A p₂) cA
        have h2 := bits_length_add_le (oracleComplexity A p₁) (oracleComplexity A p₂)
        omega
      omega
    -- Step 5: assemble `K(p | q) ≤ K(p | p*) + K(p* | q) + O(1)` with
    -- `K(p | p*) ≤ K(p | p*, K(p*)) + K(natCode K(p*)) + O(1)`.
    have a1 := hcT p (pairCode p₁ p₂) (pairCode q₁ q₂)
    have a2 := hcC p (pairCode p₁ p₂) (oracleComplexity A (pairCode p₁ p₂))
    have hE : oraclePrefixComplexityNat A p (pairCode q₁ q₂) ≤
        (2 * c₁ + 3 * cB₁) * (L₁.budget r + 1) + (2 * c₂ + 3 * cB₂) * (L₂.budget s + 1) +
          (2 * (cP + cL + cR) + (cS + cW + cU + cX) + 3 * (Nat.bits cA).length + 6 +
            cNP + cC + cT) := by
      have e1 : (2 * c₁ + 3 * cB₁) * (L₁.budget r + 1) =
          2 * (c₁ * (L₁.budget r + 1)) + 3 * (cB₁ * (L₁.budget r + 1)) := by ring
      have e2 : (2 * c₂ + 3 * cB₂) * (L₂.budget s + 1) =
          2 * (c₂ * (L₂.budget s + 1)) + 3 * (cB₂ * (L₂.budget s + 1)) := by ring
      rw [e1, e2]
      omega
    exact hE.trans (budget_combine _ _ _ _ _)
  bits_le := by
    obtain ⟨cB₁, hcB₁⟩ := L₁.bits_le
    obtain ⟨cB₂, hcB₂⟩ := L₂.bits_le
    obtain ⟨cA, hcA⟩ := oracleComplexity_pair_le_add A
    refine ⟨cB₁ + cB₂ + ((Nat.bits cA).length + 2), ?_⟩
    rintro ⟨r, s⟩ p hp
    obtain ⟨p₁, hp₁⟩ := L₁.exists_min r
    obtain ⟨p₂, hp₂⟩ := L₂.exists_min s
    have hmem : pairCode p₁ p₂ ∈
        {w | ∃ q₁ ∈ L₁.names r, ∃ q₂ ∈ L₂.names s, w = pairCode q₁ q₂} :=
      ⟨p₁, hp₁.1, p₂, hp₂.1, rfl⟩
    have hKp : oracleComplexity A p ≤ oracleComplexity A (pairCode p₁ p₂) := hp.2 _ hmem
    have a2 := hcA p₁ p₂
    have a3 := hcB₁ r p₁ hp₁
    have a4 := hcB₂ s p₂ hp₂
    have hmono : (Nat.bits (oracleComplexity A p)).length ≤
        (Nat.bits (oracleComplexity A p₁ + oracleComplexity A p₂ + cA)).length := by
      simp only [Nat.size_eq_bits_len]
      exact Nat.size_le_size (hKp.trans a2)
    have h1 := bits_length_add_le (oracleComplexity A p₁ + oracleComplexity A p₂) cA
    have h2 := bits_length_add_le (oracleComplexity A p₁) (oracleComplexity A p₂)
    have hE : (Nat.bits (oracleComplexity A p)).length ≤
        cB₁ * (L₁.budget r + 1) + cB₂ * (L₂.budget s + 1) + ((Nat.bits cA).length + 2) := by
      omega
    exact hE.trans (budget_combine _ _ _ _ _)

/-- Membership in the names of a product. -/
theorem mem_prod_names (hA : OracleSymmetryLower A) {ι₁ ι₂ : Type*}
    (L₁ : LocatedFamily A ι₁) (L₂ : LocatedFamily A ι₂) (rs : ι₁ × ι₂) (w : BitString) :
    w ∈ (L₁.prod hA L₂).names rs ↔
      ∃ q₁ ∈ L₁.names rs.1, ∃ q₂ ∈ L₂.names rs.2, w = pairCode q₁ q₂ := Iff.rfl

/-- The budget of a product is the sum of the budgets. -/
theorem prod_budget (hA : OracleSymmetryLower A) {ι₁ ι₂ : Type*}
    (L₁ : LocatedFamily A ι₁) (L₂ : LocatedFamily A ι₂) (rs : ι₁ × ι₂) :
    (L₁.prod hA L₂).budget rs = L₁.budget rs.1 + L₂.budget rs.2 := rfl

/-- **Joint versus marginal minimizers** (Lemma 4.3 of the notes): the pair of marginal
minimizers is at most `O(budget)` more complex than a joint minimizer.
Blueprint node `split:product`. -/
theorem complexity_pair_min_le (hA : OracleSymmetryLower A) {ι₁ ι₂ : Type*}
    (L₁ : LocatedFamily A ι₁) (L₂ : LocatedFamily A ι₂) :
    ∃ c : ℕ, ∀ (r : ι₁) (s : ι₂) p₁ p₂, IsMinName A (L₁.names r) p₁ →
      IsMinName A (L₂.names s) p₂ →
        oracleComplexity A (pairCode p₁ p₂) ≤
          (L₁.prod hA L₂).complexity (r, s) + c * (L₁.budget r + L₂.budget s + 1) := by
  obtain ⟨cT, hcT⟩ := (L₁.prod hA L₂).transfer
  obtain ⟨cL, hcL⟩ := oraclePrefixComplexityNat_le_oracleComplexity A
  obtain ⟨cR, hcR⟩ := oraclePrefixComplexityNat_triangle A
  obtain ⟨c₁, hc₁⟩ := L₁.transfer
  obtain ⟨c₂, hc₂⟩ := L₂.transfer
  obtain ⟨cP, hcP⟩ := oraclePrefixComplexityNat_pair_le_add A
  obtain ⟨cDL, hcDL⟩ := oraclePrefixComplexityNat_cond_pair_left_le A
  obtain ⟨cDR, hcDR⟩ := oraclePrefixComplexityNat_cond_pair_right_le A
  refine ⟨c₁ + c₂ + (cP + cDL + cDR + cR + cL), fun r s p₁ p₂ hp₁ hp₂ => ?_⟩
  obtain ⟨p, hp⟩ := (L₁.prod hA L₂).exists_min (r, s)
  obtain ⟨u₁, hu₁, u₂, hu₂, hpu⟩ := hp.1
  rw [(L₁.prod hA L₂).complexity_eq hp]
  -- `K(p*) ≤ K(p) + K(p* | p) + O(1)` and `K(p* | p) ≤ K(p₁ | u₁) + K(p₂ | u₂) + O(1)`.
  have a1 := hcR (pairCode p₁ p₂) p []
  have a2 := hcL p []
  subst hpu
  have a3 := hcP p₁ p₂ (pairCode u₁ u₂)
  have a4 := hcDL p₁ u₁ u₂
  have a5 := hcDR p₂ u₁ u₂
  have a6 := hc₁ r u₁ hu₁ p₁ hp₁
  have a7 := hc₂ s u₂ hu₂ p₂ hp₂
  have a8 : oraclePrefixComplexityNat A (pairCode u₁ u₂) [] =
      oracleComplexity A (pairCode u₁ u₂) := rfl
  have a9 : oraclePrefixComplexityNat A (pairCode p₁ p₂) [] =
      oracleComplexity A (pairCode p₁ p₂) := rfl
  have hE : oracleComplexity A (pairCode p₁ p₂) ≤ oracleComplexity A (pairCode u₁ u₂) +
      (c₁ * (L₁.budget r + 1) + c₂ * (L₂.budget s + 1) + (cP + cDL + cDR + cR + cL)) := by
    omega
  exact hE.trans (Nat.add_le_add_left (budget_combine _ _ _ _ _) _)

/-- The joint complexity is at most the sum of the marginal complexities plus a constant.
Blueprint node `split:product`. -/
theorem prod_complexity_le (hA : OracleSymmetryLower A) {ι₁ ι₂ : Type*}
    (L₁ : LocatedFamily A ι₁) (L₂ : LocatedFamily A ι₂) :
    ∃ c : ℕ, ∀ (r : ι₁) (s : ι₂),
      (L₁.prod hA L₂).complexity (r, s) ≤ L₁.complexity r + L₂.complexity s + c := by
  obtain ⟨cA, hcA⟩ := oracleComplexity_pair_le_add A
  refine ⟨cA, fun r s => ?_⟩
  obtain ⟨p₁, hp₁⟩ := L₁.exists_min r
  obtain ⟨p₂, hp₂⟩ := L₂.exists_min s
  rw [L₁.complexity_eq hp₁, L₂.complexity_eq hp₂]
  exact ((L₁.prod hA L₂).complexity_le ⟨p₁, hp₁.1, p₂, hp₂.1, rfl⟩).trans (hcA p₁ p₂)

end LocatedFamily

end Kolmogorov.PointToSet
