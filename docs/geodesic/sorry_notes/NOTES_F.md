# Notes on Chapter F (`Geodesic/PlaqueNeighborhoods.lean`)

Status (wave 2): nothing needed repair; the file type-checks with zero errors against the updated
Chapters B–E (statements unchanged; `net_approx`'s statement is unchanged and `SmallPlaques` is
only used as a hypothesis). It inherits the uniqueness gap of Chapter E through `net_approx`
(see NOTES_E.md): if the base point of `net_approx`/`effective_neighborhoods` is restricted to a
compact regular set, the dependency becomes sorry-free.

Wave 2 final: `effective_neighborhoods` takes `{Px} (hPx) (hPxR)` and quantifies `∀ x ∈ Px` (statement in NOTES_E.md); proof repaired (`net_approx … hPx hPxR`, `hPxR hx` for the regularity of `x`). Zero errors, zero sorries.

Final statement of `effective_neighborhoods` (with `Px` and the exported box membership `x ∈ (G.box j).U`):

```lean
theorem effective_neighborhoods {Pp Pm : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg) {Px : Set X} (hPx : IsCompact Px)
    (hPxR : Px ⊆ G.Reg) (ρ : ℚ) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pp ∪ Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ nbhd : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ →. List (ℕ × ℚ) × List (ℕ × ℚ) × ℚ × ℚ,
        PartrecIn {charOracle B} nbhd ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ (j : Fin G.nBoxes) (r : ℚ) (εx : ℝ), x ∈ (G.box j).U ∧ 0 < r ∧ 0 < εx ∧
            ∀ Tp Tm : ℕ, G.φ (Tp : ℝ) x ∈ Pp → G.φ (-(Tm : ℝ)) x ∈ Pm →
            ∀ ip im : ℕ, P.ι ip ∈ bowenBall G.f (Tp + 1) x (min ε (r / 8)) →
              P.ι im ∈ bowenBall G.finv (Tm + 1) x (min ε (r / 8)) →
              (nbhd (j, ip, im, Tp, Tm, r)).Dom ∧
                ∀ out ∈ nbhd (j, ip, im, Tp, Tm, r),
                  G.plaque .cs εx x ⊆ ballUnion P out.1 ∧
                  ballUnion P out.1 ⊆ Metric.thickening (C₂ * G.scalePlus ρ Tp x) (G.Wloc .cs x) ∧
                  G.plaque .cu εx x ⊆ ballUnion P out.2.1 ∧
                  ballUnion P out.2.1 ⊆
                    Metric.thickening (C₂ * G.scaleMinus ρ Tm x) (G.Wloc .cu x) ∧
                  0 < out.2.2.1 ∧ G.scalePlus (ρ / 2) Tp x ≤ out.2.2.1 ∧
                    (out.2.2.1 : ℝ) ≤ G.scalePlus ρ Tp x ∧
                  0 < out.2.2.2 ∧ G.scaleMinus (ρ / 2) Tm x ≤ out.2.2.2 ∧
                    (out.2.2.2 : ℝ) ≤ G.scaleMinus ρ Tm x)
```
