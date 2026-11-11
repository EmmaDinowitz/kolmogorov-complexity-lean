/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import Mathlib.Computability.Primrec.Basic
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Base-`N` numerals with a leading digit

An itinerary of `m` symbols from an alphabet of size `N` is coded by the natural
`Nat.ofDigits N (D ++ [1])`, the base-`N` numeral with digits `D` and a leading `1`: the
leading digit makes the length recoverable (`ofDigits_append_one_bounds`), and the `k`-th
symbol is the `k`-th base-`N` digit (`ofDigits_append_one_digit`). The digit extraction
`digitAt` and the powers `natPowRec` are written by primitive recursion so that their
primitive recursiveness is immediate. Blueprint node `eff:numerals`.
-/

namespace Kolmogorov.PointToSet

/-- The `k`-th base-`N` digit of `J`, computed by `k` successive divisions (a primitive
recursive form of `J / N ^ k % N`). -/
def digitAt (N J k : ℕ) : ℕ :=
  (Nat.rec (motive := fun _ ↦ ℕ) J (fun _ ih ↦ ih / N) k) % N

/-- `digitAt N J k` is the `k`-th base-`N` digit `J / N ^ k % N`. -/
lemma digitAt_eq (N J k : ℕ) : digitAt N J k = J / N ^ k % N := by
  unfold digitAt
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    change (Nat.rec (motive := fun _ ↦ ℕ) J (fun _ ih ↦ ih / N) k) / N = J / N ^ (k + 1)
    rw [ih, Nat.div_div_eq_div_mul, pow_succ]

/-- Digit extraction is primitive recursive in the numeral and the position. -/
lemma primrec_digitAt (N : ℕ) : Primrec₂ (digitAt N) := by
  have h : Primrec fun p : ℕ × ℕ ↦
      Nat.rec (motive := fun _ ↦ ℕ) p.1 (fun _ ih ↦ ih / N) p.2 :=
    Primrec.nat_rec' Primrec.snd Primrec.fst
      (Primrec.nat_div.comp (Primrec.snd.comp Primrec.snd) (Primrec.const N)).to₂
  exact Primrec.nat_mod.comp h (Primrec.const N)

/-- Powers of a fixed base by primitive recursion. -/
def natPowRec (N t : ℕ) : ℕ := Nat.rec (motive := fun _ ↦ ℕ) 1 (fun _ ih ↦ ih * N) t

/-- `natPowRec N t` is the power `N ^ t`. -/
lemma natPowRec_eq (N t : ℕ) : natPowRec N t = N ^ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change natPowRec N t * N = N ^ (t + 1)
    rw [ih, pow_succ]

/-- Powers of a fixed base are primitive recursive in the exponent. -/
lemma primrec_natPowRec (N : ℕ) : Primrec (natPowRec N) :=
  Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp Primrec.snd (Primrec.const N)).to₂

/-- Digits of a base-`N` numeral with a leading digit `1` appended. -/
lemma ofDigits_append_one_digit {N : ℕ} (hN : 2 ≤ N) (D : List ℕ)
    (hD : ∀ d ∈ D, d < N) {k : ℕ} (hk : k < D.length) :
    Nat.ofDigits N (D ++ [1]) / N ^ k % N = D[k] := by
  have h1 : Nat.digits N (Nat.ofDigits N (D ++ [1])) = D ++ [1] := by
    refine Nat.digits_ofDigits N (by omega) _ ?_ ?_
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hD d hd
      · rw [List.mem_singleton.mp hd]
        omega
    · intro _
      rw [List.getLast_append_singleton]
      exact one_ne_zero
  rw [Nat.self_div_pow_eq_ofDigits_drop k _ hN, h1, List.drop_append_of_le_length hk.le,
    List.drop_eq_getElem_cons hk, List.cons_append, Nat.ofDigits_cons,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hD _ (List.getElem_mem hk))]

/-- Size of a base-`N` numeral with a leading digit `1` appended. -/
lemma ofDigits_append_one_bounds {N : ℕ} (hN : 2 ≤ N) (D : List ℕ)
    (hD : ∀ d ∈ D, d < N) :
    N ^ D.length ≤ Nat.ofDigits N (D ++ [1]) ∧
      Nat.ofDigits N (D ++ [1]) + 1 ≤ 2 * N ^ D.length := by
  rw [Nat.ofDigits_append, Nat.ofDigits_singleton, mul_one]
  have := Nat.ofDigits_lt_base_pow_length (by omega : 1 < N) hD
  constructor <;> omega

end Kolmogorov.PointToSet
