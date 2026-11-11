/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.Basic
import KolmogorovMathlib.Oracle.Universal.Enumeration
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun

/-!
# Closure properties of relative computability and enumerability

Relative computability, relative partial recursiveness and relatively computable real families
transfer to every Turing-stronger oracle (`computableIn_mono_oracle`, `partrecIn_mono`,
`isComputableRealFamilyIn_mono_oracle`; `IsREIn.mono_oracle` is in `Oracle/Basic.lean`).
Relatively enumerable predicates are closed under disjunction (`IsREIn.or`, by interleaving two
enumerations), finite uniformization over `Fin n` (`isREIn_fin_uniform`) and bounded universal
quantification over the positions of a list (`IsREIn.list_forall_get`), and every one of them
has an oracle-computable prefix enumeration (`IsREIn.exists_prefixList`). A relatively partial
recursive program can be run on every member of a list (`PartrecIn.exists_list_mapM`).
Relatively computable real families are closed under computable reindexing
(`IsComputableRealFamilyIn.comp`), and strict comparisons of their values with rationals are
relatively enumerable in both directions (`birkhoff_computableIn_lt`, `birkhoff_computableIn_gt`,
with the computable dyadic sequence `computable_rat_inv_two_pow`).
Blueprint node `eff:closure`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

section monoOracle

variable {A B : Set ℕ}

/-- A Boolean conditional preserves computability relative to a fixed oracle family. -/
lemma computable_in_cond {α σ : Type*} [Primcodable α] [Primcodable σ]
    {O : Set (ℕ →. ℕ)} {c : α → Bool} {f g : α → σ}
    (hc : ComputableIn O c) (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a ↦ cond (c a) (f a) (g a)) :=
  (Computable.cond Computable.fst (Computable.fst.comp Computable.snd)
    (Computable.snd.comp Computable.snd)).computableIn.comp (hc.pair (hf.pair hg))

/-- Relative computability transfers to every Turing-stronger oracle. -/
theorem computableIn_mono_oracle {α σ : Type*} [Primcodable α] [Primcodable σ] {f : α → σ}
    (hf : ComputableIn {charOracle A} f) (hAB : charOracle A ≤ᵀ charOracle B) :
    ComputableIn {charOracle B} f := by
  refine RecursiveIn.subst hf fun g hg ↦ ?_
  obtain rfl := Set.mem_singleton_iff.mp hg
  exact hAB

/-- Computable real families transfer to every Turing-stronger oracle. -/
theorem isComputableRealFamilyIn_mono_oracle {α : Type*} [Primcodable α] {v : α → ℝ}
    (hv : IsComputableRealFamilyIn A v) (hAB : charOracle A ≤ᵀ charOracle B) :
    IsComputableRealFamilyIn B v := by
  obtain ⟨q, hq, herr⟩ := hv
  exact ⟨q, computableIn_mono_oracle hq hAB, herr⟩

end monoOracle

/-- A program partial recursive in `B` is partial recursive in every `A` above `B`. -/
theorem partrecIn_mono (A : Set ℕ) {α β : Type*} [Primcodable α] [Primcodable β] {B : Set ℕ}
    (hBA : charOracle B ≤ᵀ charOracle A) {F : α →. β} (hF : PartrecIn {charOracle B} F) :
    PartrecIn {charOracle A} F := by
  refine RecursiveIn.subst hF fun g hg ↦ ?_
  obtain rfl := Set.mem_singleton_iff.mp hg
  exact hBA

section closure

variable {A : Set ℕ}

/-- The disjunction of two relatively enumerable predicates is relatively enumerable
(interleave two enumerations). -/
theorem IsREIn.or {α : Type*} [Primcodable α] {F G : α → Prop} (hF : IsREIn A F)
    (hG : IsREIn A G) : IsREIn A fun x ↦ F x ∨ G x := by
  obtain ⟨e, he, hF'⟩ := (relative_enumeration A F).mp hF
  obtain ⟨e', he', hG'⟩ := (relative_enumeration A G).mp hG
  refine (relative_enumeration A _).mpr
    ⟨fun t ↦ cond (decide (t % 2 = 0)) (e (t / 2)) (e' (t / 2)), ?_, fun x ↦ ?_⟩
  · have hc : Computable fun t : ℕ ↦ decide (t % 2 = 0) :=
      (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
        (Primrec.const 0)).decide.to_comp
    have hd : Computable fun t : ℕ ↦ t / 2 :=
      (Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp
    exact computable_in_cond hc.computableIn (he.comp hd.computableIn) (he'.comp hd.computableIn)
  · constructor
    · rintro (hx | hx)
      · obtain ⟨t, ht⟩ := (hF' x).mp hx
        refine ⟨2 * t, ?_⟩
        have h2 : 2 * t / 2 = t := by omega
        simp [h2, ht]
      · obtain ⟨t, ht⟩ := (hG' x).mp hx
        refine ⟨2 * t + 1, ?_⟩
        have h2 : (2 * t + 1) / 2 = t := by omega
        simp [h2, ht]
    · rintro ⟨t, ht⟩
      by_cases h : t % 2 = 0
      · simp only [h, decide_true, Bool.cond_true] at ht
        exact Or.inl ((hF' x).mpr ⟨_, ht⟩)
      · simp only [h, decide_false, Bool.cond_false] at ht
        exact Or.inr ((hG' x).mpr ⟨_, ht⟩)

/-- A predicate on `Fin n × β` whose every section is relatively enumerable is relatively
enumerable (finite disjunction over the first coordinate). -/
theorem isREIn_fin_uniform {n : ℕ} {β : Type*} [Primcodable β] {F : Fin n → β → Prop}
    (hF : ∀ j, IsREIn A (F j)) : IsREIn A fun w : Fin n × β ↦ F w.1 w.2 := by
  have key : ∀ s : Finset (Fin n), IsREIn A fun w : Fin n × β ↦ ∃ j ∈ s, j = w.1 ∧ F j w.2 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h : (fun w : Fin n × β ↦ ∃ j ∈ (∅ : Finset (Fin n)), j = w.1 ∧ F j w.2) =
          fun _ ↦ False := by
        funext w
        simp
      rw [h]
      exact isREIn_empty A
    · intro j s _ ih
      have h : (fun w : Fin n × β ↦ ∃ j' ∈ insert j s, j' = w.1 ∧ F j' w.2) =
          fun w ↦ (j = w.1 ∧ F j w.2) ∨ ∃ j' ∈ s, j' = w.1 ∧ F j' w.2 := by
        ext w
        simp only [Finset.mem_insert, exists_eq_or_imp]
      rw [h]
      refine IsREIn.or ((isREIn_of_computable_decide ?_).and
        ((hF j).comp Computable.snd.computableIn)) ih
      exact (Primrec.eq.comp (Primrec.const j) Primrec.fst).decide.to_comp
  have h := key Finset.univ
  have heq : (fun w : Fin n × β ↦ ∃ j ∈ (Finset.univ : Finset (Fin n)), j = w.1 ∧ F j w.2) =
      fun w ↦ F w.1 w.2 := by
    ext w
    simp
  rw [heq] at h
  exact h

/-- A prefix enumeration of a relatively enumerable predicate on `ι × β`: oracle-computable lists
`L (i, t)` of elements `b` with `E (i, b)` listed within the first `t` stages, sound, monotone in
`t`, exhausting every listed element, and containing any finite set of listed elements at some
stage. -/
theorem IsREIn.exists_prefixList {ι β : Type*} [Primcodable ι] [Primcodable β] {E : ι × β → Prop}
    (hE : IsREIn A E) :
    ∃ L : ι × ℕ → List β, ComputableIn {charOracle A} L ∧
      (∀ i t b, b ∈ L (i, t) → E (i, b)) ∧
      (∀ i t t', t ≤ t' → ∀ b ∈ L (i, t), b ∈ L (i, t')) ∧
      (∀ i b, E (i, b) → ∃ t, b ∈ L (i, t)) ∧
      ∀ i (S : Finset β), (∀ b ∈ S, E (i, b)) → ∃ t, ∀ b ∈ S, b ∈ L (i, t) := by
  obtain ⟨e, he, henum⟩ := (relative_enumeration A E).mp hE
  let step : ι × List β × Option (ι × β) → List β := fun w ↦
    Option.casesOn (motive := fun _ ↦ List β) w.2.2 w.2.1 fun v ↦
      if Encodable.encode v.1 = Encodable.encode w.1 then v.2 :: w.2.1 else w.2.1
  have hstep : Computable step := by
    refine Computable.option_casesOn (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd) (Primrec.to_comp ?_)
    exact Primrec.ite
      (Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.encode.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  let L : ι × ℕ → List β := fun it ↦
    @Nat.rec (fun _ ↦ List β) [] (fun s ih ↦ step (it.1, ih, e s)) it.2
  have hL : ComputableIn {charOracle A} L := by
    refine ComputableIn.nat_rec (f := fun it : ι × ℕ ↦ it.2) (g := fun _ ↦ ([] : List β))
      (h := fun it sih ↦ step (it.1, sih.2, e sih.1)) ComputableIn.snd (ComputableIn.const [])
      (ComputableIn₂.mk ?_)
    exact hstep.computableIn.comp ((ComputableIn.fst.comp ComputableIn.fst).pair
      ((ComputableIn.snd.comp ComputableIn.snd).pair
        (he.comp (ComputableIn.fst.comp ComputableIn.snd))))
  have hmem : ∀ (i : ι) (t : ℕ) (b : β), b ∈ L (i, t) ↔ ∃ s < t, e s = some (i, b) := by
    intro i t b
    induction t with
    | zero => simp [L]
    | succ t ih =>
      have hstep_eq : L (i, t + 1) = step (i, L (i, t), e t) := rfl
      rw [hstep_eq]
      cases het : e t with
      | none =>
        change b ∈ L (i, t) ↔ _
        rw [ih]
        constructor
        · rintro ⟨s, hs, hes⟩
          exact ⟨s, by omega, hes⟩
        · rintro ⟨s, hs, hes⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
          · exact ⟨s, hs, hes⟩
          · rw [het] at hes
            exact absurd hes (by simp)
      | some v =>
        change b ∈ (if Encodable.encode v.1 = Encodable.encode i then v.2 :: L (i, t) else L (i, t))
          ↔ _
        split_ifs with hv
        · have hv' : v.1 = i := Encodable.encode_injective hv
          rw [List.mem_cons, ih]
          constructor
          · rintro (rfl | ⟨s, hs, hes⟩)
            · exact ⟨t, Nat.lt_succ_self t, by rw [het, ← hv']⟩
            · exact ⟨s, by omega, hes⟩
          · rintro ⟨s, hs, hes⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
            · exact Or.inr ⟨s, hs, hes⟩
            · rw [het] at hes
              exact Or.inl (by rw [Option.some_injective _ hes])
        · rw [ih]
          constructor
          · rintro ⟨s, hs, hes⟩
            exact ⟨s, by omega, hes⟩
          · rintro ⟨s, hs, hes⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
            · exact ⟨s, hs, hes⟩
            · rw [het] at hes
              have hv2 : v = (i, b) := Option.some_injective _ hes
              exact (hv (by rw [hv2])).elim
  have hmono : ∀ i t t', t ≤ t' → ∀ b ∈ L (i, t), b ∈ L (i, t') := by
    intro i t t' htt b hb
    obtain ⟨s, hs, hes⟩ := (hmem i t b).mp hb
    exact (hmem i t' b).mpr ⟨s, by omega, hes⟩
  have hex : ∀ i b, E (i, b) → ∃ t, b ∈ L (i, t) := by
    intro i b hb
    obtain ⟨s, hs⟩ := (henum (i, b)).mp hb
    exact ⟨s + 1, (hmem i (s + 1) b).mpr ⟨s, Nat.lt_succ_self s, hs⟩⟩
  refine ⟨L, hL, fun i t b hb ↦ ?_, hmono, hex, fun i S ↦ ?_⟩
  · obtain ⟨s, _, hes⟩ := (hmem i t b).mp hb
    exact (henum (i, b)).mpr ⟨s, hes⟩
  · classical
    refine Finset.induction_on S ?_ ?_
    · exact fun _ ↦ ⟨0, fun b hb ↦ by simp at hb⟩
    · intro b S _ ih h
      obtain ⟨t, ht⟩ := ih fun b' hb' ↦ h b' (Finset.mem_insert_of_mem hb')
      obtain ⟨t', ht'⟩ := hex i b (h b (Finset.mem_insert_self b S))
      refine ⟨max t t', fun b' hb' ↦ ?_⟩
      rcases Finset.mem_insert.mp hb' with rfl | hb'
      · exact hmono i t' _ (le_max_right _ _) b' ht'
      · exact hmono i t _ (le_max_left _ _) b' (ht b' hb')

/-- Running a relatively partial recursive program on every member of a list: the result lists
the inputs with their outputs, is defined exactly when every run halts, and is partial
recursive in the oracle. -/
theorem PartrecIn.exists_list_mapM {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] [Inhabited β] {g : α → β →. γ} (hg : PartrecIn₂ {charOracle A} g) :
    ∃ F : α × List β →. List (β × γ), PartrecIn {charOracle A} F ∧
      (∀ a L, (F (a, L)).Dom ↔ ∀ b ∈ L, (g a b).Dom) ∧
      ∀ a L out, out ∈ F (a, L) → out.map Prod.fst = L ∧ ∀ e ∈ out, e.2 ∈ g a e.1 := by
  let step : α × List β → ℕ × List (β × γ) →. List (β × γ) := fun aL mo ↦
    (g aL.1 (aL.2.getD mo.1 default)).map fun c ↦ mo.2 ++ [(aL.2.getD mo.1 default, c)]
  have hstep : PartrecIn₂ {charOracle A} step := by
    have h1 : ComputableIn {charOracle A} fun p : (α × List β) × (ℕ × List (β × γ)) ↦
        (p.1.1, p.1.2.getD p.2.1 default) :=
      ((Computable.fst.comp Computable.fst).pair ((Primrec.list_getD default).to_comp.comp
        (Computable.snd.comp Computable.fst) (Computable.fst.comp Computable.snd))).computableIn
    have h2 : ComputableIn₂ {charOracle A}
        fun (p : (α × List β) × (ℕ × List (β × γ))) (c : γ) ↦
          p.2.2 ++ [(p.1.2.getD p.2.1 default, c)] :=
      (Primrec.list_concat.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
        (((Primrec.list_getD default).to_comp.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst))
          (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair
            Computable.snd)).computableIn
    have hg' : PartrecIn {charOracle A} fun q : α × β ↦ g q.1 q.2 := hg
    exact PartrecIn.map (PartrecIn.comp hg' h1) h2
  -- the partial result after `n` steps
  let Fn : α × List β → ℕ → Part (List (β × γ)) := fun aL n ↦
    @Nat.rec (fun _ ↦ Part (List (β × γ))) (Part.some [])
      (fun m ih ↦ ih.bind fun out ↦ step aL (m, out)) n
  have hF : PartrecIn {charOracle A} fun aL : α × List β ↦ Fn aL aL.2.length :=
    relative_closure_nat_rec A (fun aL : α × List β ↦ aL.2.length) (fun _ ↦ Part.some [])
      step (Computable.list_length.comp Computable.snd).computableIn
      (ComputableIn.const ([] : List (β × γ))).partrecIn hstep
  have hspec : ∀ (a : α) (L : List β) (n : ℕ),
      (∀ out, out ∈ Fn (a, L) n →
        out.map Prod.fst = (List.range n).map (fun m ↦ L.getD m default) ∧
          ∀ e ∈ out, e.2 ∈ g a e.1) ∧
      ((∀ m < n, (g a (L.getD m default)).Dom) → ∃ out, out ∈ Fn (a, L) n) := by
    intro a L n
    induction n with
    | zero =>
      refine ⟨fun out hout ↦ ?_, fun _ ↦ ⟨[], Part.mem_some _⟩⟩
      have h : out = [] := Part.mem_some_iff.mp hout
      subst h
      simp
    | succ n ih =>
      have hsucc : Fn (a, L) (n + 1) = (Fn (a, L) n).bind fun out ↦ step (a, L) (n, out) := rfl
      refine ⟨fun out' hout' ↦ ?_, fun hdom ↦ ?_⟩
      · rw [hsucc, Part.mem_bind_iff] at hout'
        obtain ⟨out, hout, hout'⟩ := hout'
        obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hout'
        obtain ⟨hmap, hmem⟩ := ih.1 out hout
        refine ⟨?_, fun e he ↦ ?_⟩
        · rw [List.map_append, hmap, List.range_succ, List.map_append]
          rfl
        · rcases List.mem_append.mp he with he | he
          · exact hmem e he
          · have : e = (L.getD n default, c) := List.mem_singleton.mp he
            subst this
            exact hc
      · obtain ⟨out, hout⟩ := ih.2 fun m hm ↦ hdom m (Nat.lt_succ_of_lt hm)
        obtain ⟨c, hc⟩ := Part.dom_iff_mem.mp (hdom n (Nat.lt_succ_self n))
        refine ⟨out ++ [(L.getD n default, c)], ?_⟩
        rw [hsucc, Part.mem_bind_iff]
        exact ⟨out, hout, (Part.mem_map_iff _).mpr ⟨c, hc, rfl⟩⟩
  have hrange : ∀ L : List β, (List.range L.length).map (fun m ↦ L.getD m default) = L := by
    intro L
    refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]
  refine ⟨fun aL ↦ Fn aL aL.2.length, hF, fun a L ↦ ?_, fun a L out hout ↦ ?_⟩
  · constructor
    · intro hd
      obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp hd
      obtain ⟨hmap, hmem⟩ := (hspec a L L.length).1 out hout
      rw [hrange] at hmap
      intro b hb
      rw [← hmap] at hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
      exact Part.dom_iff_mem.mpr ⟨e.2, hmem e he⟩
    · intro h
      refine Part.dom_iff_mem.mpr ((hspec a L L.length).2 fun m hm ↦ ?_)
      rw [List.getD_eq_getElem _ _ hm]
      exact h _ (List.getElem_mem hm)
  · obtain ⟨hmap, hmem⟩ := (hspec a L L.length).1 out hout
    rw [hrange] at hmap
    exact ⟨hmap, hmem⟩

end closure

/-- Bounded universal quantification over the positions of a list preserves relative
enumerability: the certificate is a stage of the enumeration by which every required
instance has appeared. Blueprint node `geo:orbit-extension` (auxiliary). -/
theorem IsREIn.list_forall_get {α β : Type*} [Primcodable α] [Primcodable β] {A : Set ℕ}
    {F : α × ℕ × β → Prop} (hF : IsREIn A F) :
    IsREIn A fun d : α × List β ↦
      ∀ k : ℕ, ∀ h : k < d.2.length, F (d.1, k, d.2.get ⟨k, h⟩) := by
  obtain ⟨e, he, henum⟩ := (relative_enumeration A F).mp hF
  -- `hitO ((x, k, some b), t)`: some stage `s < t` of the enumeration lists `(x, k, b)`
  let hitO : (α × ℕ × Option β) × ℕ → Bool := fun w ↦
    Nat.rec (motive := fun _ ↦ Bool) false (fun s ih ↦ ih ||
      (Encodable.encode (e s) ==
        Encodable.encode (w.1.2.2.map fun b ↦ (w.1.1, w.1.2.1, b)))) w.2
  have hhitO : ComputableIn {charOracle A} hitO := by
    refine ComputableIn.nat_rec (f := fun w : (α × ℕ × Option β) × ℕ ↦ w.2)
      (g := fun _ ↦ false)
      (h := fun w sih ↦ sih.2 || (Encodable.encode (e sih.1) ==
        Encodable.encode (w.1.2.2.map fun b ↦ (w.1.1, w.1.2.1, b))))
      ComputableIn.snd (ComputableIn.const false) (ComputableIn₂.mk ?_)
    have h1 : ComputableIn {charOracle A}
        fun p : ((α × ℕ × Option β) × ℕ) × (ℕ × Bool) ↦ Encodable.encode (e p.2.1) :=
      Computable.encode.computableIn.comp (he.comp (ComputableIn.fst.comp ComputableIn.snd))
    have h2 : Primrec fun p : ((α × ℕ × Option β) × ℕ) × (ℕ × Bool) ↦
        Encodable.encode (p.1.1.2.2.map fun b ↦ (p.1.1.1, p.1.1.2.1, b)) := by
      refine Primrec.encode.comp ?_
      refine Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        ?_
      exact (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        ((Primrec.fst.comp
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
          Primrec.snd)
    have h3 : ComputableIn {charOracle A} fun p : ((α × ℕ × Option β) × ℕ) × (ℕ × Bool) ↦
        (Encodable.encode (e p.2.1) ==
          Encodable.encode (p.1.1.2.2.map fun b ↦ (p.1.1.1, p.1.1.2.1, b))) :=
      Primrec.beq.to_comp.computableIn₂.comp h1 h2.to_comp.computableIn
    exact Primrec.or.to_comp.computableIn₂.comp (ComputableIn.snd.comp ComputableIn.snd) h3
  have hhitO_iff : ∀ (x : α) (k : ℕ) (b : β) (t : ℕ),
      hitO ((x, k, some b), t) = true ↔ ∃ s < t, e s = some (x, k, b) := by
    intro x k b t
    induction t with
    | zero => simp [hitO]
    | succ t ih =>
      have hstep : hitO ((x, k, some b), t + 1) = (hitO ((x, k, some b), t) ||
          (Encodable.encode (e t) == Encodable.encode (some (x, k, b)))) := rfl
      rw [hstep, Bool.or_eq_true, ih, beq_iff_eq, Encodable.encode_inj]
      constructor
      · rintro (⟨s, hs, hes⟩ | hes)
        · exact ⟨s, by omega, hes⟩
        · exact ⟨t, Nat.lt_succ_self t, hes⟩
      · rintro ⟨s, hs, hes⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
        · exact Or.inl ⟨s, hs, hes⟩
        · exact Or.inr hes
  -- `ok (d, t)`: every position of the list is certified by stage `t`
  let ok : (α × List β) × ℕ → Bool := fun d ↦
    Nat.rec (motive := fun _ ↦ Bool) true
      (fun k ih ↦ ih && hitO ((d.1.1, k, d.1.2[k]?), d.2)) d.1.2.length
  have hok : ComputableIn {charOracle A} ok := by
    refine ComputableIn.nat_rec (f := fun d : (α × List β) × ℕ ↦ d.1.2.length)
      (g := fun _ ↦ true)
      (h := fun d kih ↦ kih.2 && hitO ((d.1.1, kih.1, d.1.2[kih.1]?), d.2))
      (Computable.list_length.comp (Computable.snd.comp Computable.fst)).computableIn
      (ComputableIn.const true) (ComputableIn₂.mk ?_)
    have harg : Computable fun p : ((α × List β) × ℕ) × (ℕ × Bool) ↦
        ((p.1.1.1, p.2.1, p.1.1.2[p.2.1]?), p.1.2) :=
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.fst.comp Computable.snd).pair
          (Primrec.list_getElem?.to_comp.comp
            (Computable.snd.comp (Computable.fst.comp Computable.fst))
            (Computable.fst.comp Computable.snd)))).pair (Computable.snd.comp Computable.fst)
    exact Primrec.and.to_comp.computableIn₂.comp (ComputableIn.snd.comp ComputableIn.snd)
      (hhitO.comp harg.computableIn)
  have hok_iff : ∀ (x : α) (l : List β) (t : ℕ), ok ((x, l), t) = true ↔
      ∀ k : ℕ, ∀ h : k < l.length, ∃ s < t, e s = some (x, k, l.get ⟨k, h⟩) := by
    intro x l t
    have hgen : ∀ N : ℕ, (Nat.rec (motive := fun _ ↦ Bool) true
        (fun k ih ↦ ih && hitO ((x, k, l[k]?), t)) N = true) ↔
        ∀ k < N, hitO ((x, k, l[k]?), t) = true := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        have hstep : (Nat.rec (motive := fun _ ↦ Bool) true
            (fun k ih ↦ ih && hitO ((x, k, l[k]?), t)) (N + 1)) =
            (Nat.rec (motive := fun _ ↦ Bool) true
              (fun k ih ↦ ih && hitO ((x, k, l[k]?), t)) N && hitO ((x, N, l[N]?), t)) := rfl
        rw [hstep, Bool.and_eq_true, ih]
        constructor
        · rintro ⟨h1, h2⟩ k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact h1 k hk
          · exact h2
        · intro h
          exact ⟨fun k hk ↦ h k (Nat.lt_succ_of_lt hk), h N (Nat.lt_succ_self N)⟩
    change (Nat.rec (motive := fun _ ↦ Bool) true
      (fun k ih ↦ ih && hitO ((x, k, l[k]?), t)) l.length = true) ↔ _
    rw [hgen]
    constructor
    · intro h k hk
      have h' := h k hk
      rw [List.getElem?_eq_getElem hk] at h'
      exact (hhitO_iff x k _ t).mp h'
    · intro h k hk
      rw [List.getElem?_eq_getElem hk]
      exact (hhitO_iff x k _ t).mpr (h k hk)
  have hiff : ∀ d : α × List β,
      (∀ k : ℕ, ∀ h : k < d.2.length, F (d.1, k, d.2.get ⟨k, h⟩)) ↔ ∃ t, ok (d, t) = true := by
    rintro ⟨x, l⟩
    rw [exists_congr fun t ↦ hok_iff x l t]
    constructor
    · intro h
      have hind : ∀ N, N ≤ l.length → ∃ t, ∀ k : ℕ, ∀ hk : k < l.length, k < N →
          ∃ s < t, e s = some (x, k, l.get ⟨k, hk⟩) := by
        intro N
        induction N with
        | zero => exact fun _ ↦ ⟨0, fun k _ hkN ↦ absurd hkN (Nat.not_lt_zero k)⟩
        | succ N ih =>
          intro hN
          obtain ⟨t, ht⟩ := ih (Nat.le_of_succ_le hN)
          obtain ⟨s, hs⟩ := (henum _).mp (h N (Nat.lt_of_succ_le hN))
          refine ⟨max t (s + 1), fun k hk hkN ↦ ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hkN with hkN | rfl
          · obtain ⟨s', hs', hes'⟩ := ht k hk hkN
            exact ⟨s', lt_of_lt_of_le hs' (le_max_left _ _), hes'⟩
          · exact ⟨s, lt_of_lt_of_le (Nat.lt_succ_self s) (le_max_right _ _), hs⟩
      obtain ⟨t, ht⟩ := hind l.length le_rfl
      exact ⟨t, fun k hk ↦ ht k hk hk⟩
    · rintro ⟨t, ht⟩ k hk
      obtain ⟨s, _, hs⟩ := ht k hk
      exact (henum _).mpr ⟨s, hs⟩
  have hre : IsREIn A fun p : (α × List β) × ℕ ↦ ok p = true :=
    isREIn_of_computableIn_decide A _ (hok.of_eq fun p ↦ Bool.decide_eq_true.symm)
  have h := hre.exists
  have heq : (fun d : α × List β ↦ ∃ t, ok (d, t) = true) =
      fun d ↦ ∀ k : ℕ, ∀ h : k < d.2.length, F (d.1, k, d.2.get ⟨k, h⟩) := by
    funext d
    exact propext (hiff d).symm
  rw [heq] at h
  exact h

/-! ### Computable real families: reindexing and rational comparisons -/

section realFamilies

/-- Reindexing a computable real family by a computable function preserves computability. -/
theorem IsComputableRealFamilyIn.comp {α β : Type*} [Primcodable α] [Primcodable β]
    (A : Set ℕ) (v : β → ℝ) (hv : IsComputableRealFamilyIn A v) (f : α → β) (hf : Computable f) :
    IsComputableRealFamilyIn A (v ∘ f) := by
  rcases hv with ⟨q, hq_comp, hq_bound⟩
  use fun ap ↦ q (f ap.1, ap.2)
  constructor
  · apply hq_comp.comp
    exact (hf.comp Computable.fst).pair Computable.snd |>.computableIn
  · intro i p
    exact hq_bound (f i) p

/-- Twice an inverse power of two is smaller than any positive real tolerance. -/
lemma exists_two_mul_inv_two_pow_lt (d : ℝ) (hd : 0 < d) :
    ∃ p : ℕ, (2 : ℝ) * (2^p : ℝ)⁻¹ < d := by
  have ⟨p, hp⟩ : ∃ p : ℕ, (2:ℝ)⁻¹ ^ p < d / 2 := by
    exact exists_pow_lt_of_lt_one (half_pos hd) (by norm_num)
  use p
  have h_pow : (2⁻¹ : ℝ) ^ p = (2^p : ℝ)⁻¹ := by simp [inv_pow]
  rw [h_pow] at hp
  linarith

/-- The rational sequence of inverse powers of two is computable. -/
lemma computable_rat_inv_two_pow : Computable (fun (p : ℕ) ↦ (2^p : ℚ)⁻¹) := by
  have H : (fun (p : ℕ) ↦ (2^p : ℚ)⁻¹) = fun p ↦ (1 : ℚ) / ((2^p : ℕ) : ℚ) := by
    ext p
    have h2 : ((2^p : ℕ) : ℚ) = (2:ℚ)^p := by simp
    rw [h2, inv_eq_one_div]
  rw [H]
  apply computable_of_num_den (Computable.const (1 : ℤ)) comp_pow
  · intro p
    positivity
  · intro p
    rfl

/-- Strict rational upper comparisons with a uniform computable real family are enumerable,
with the threshold part of the ambient index.
Blueprint node `metric:birkhoff`. -/
theorem birkhoff_computableIn_lt {α : Type*} [Primcodable α] (A : Set ℕ) (v : α → ℝ)
    (hv : IsComputableRealFamilyIn A v) :
    IsREIn A (fun iq : α × ℚ => v iq.1 < (iq.2 : ℝ)) := by
  rcases hv with ⟨q, hq_comp, hq_approx⟩
  let f : α × ℚ →. ℕ := fun iq ↦
    Nat.rfindOpt (fun p ↦ cond (decide (q (iq.1, p) + (2^p : ℚ)⁻¹ < iq.2)) (some p) none)
  have hf : PartrecIn {charOracle A} f := by
    apply PartrecIn.rfindOpt
    have hqArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ q (w.1.1, w.2)) :=
      hq_comp.comp ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
    have hεArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ (2^w.2 : ℚ)⁻¹) :=
      computable_rat_inv_two_pow.computableIn.comp Computable.snd.computableIn
    have hsum : ComputableIn {charOracle A}
        (fun w : (α × ℚ) × ℕ ↦ q (w.1.1, w.2) + (2^w.2 : ℚ)⁻¹) :=
      (Computable₂.computableIn₂ computable₂_ratAdd).comp hqArg hεArg
    have hrArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ w.1.2) :=
      (Computable.snd.comp Computable.fst).computableIn
    have hcmp : ComputableIn {charOracle A}
        (fun w : (α × ℚ) × ℕ ↦ decide (q (w.1.1, w.2) + (2^w.2 : ℚ)⁻¹ < w.1.2)) :=
      (Computable₂.computableIn₂ computable₂_ratLt).comp hsum hrArg
    have hsome : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ some w.2) :=
      (Primrec.option_some.to_comp.comp Computable.snd).computableIn
    have hnone : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ (none : Option ℕ)) :=
      (Computable.const none).computableIn
    have H : ComputableIn {charOracle A}
        (fun (w : (α × ℚ) × ℕ) ↦
          cond (decide (q (w.1.1, w.2) + (2^w.2 : ℚ)⁻¹ < w.1.2)) (some w.2) none) :=
      computable_in_cond hcmp hsome hnone
    exact ComputableIn₂.mk H
  use f
  constructor
  · exact hf
  · intro ⟨i, r⟩
    simp only [f]
    rw [Nat.rfindOpt_dom]
    constructor
    · intro h
      have h_sub : 0 < (r : ℝ) - v i := sub_pos.mpr h
      obtain ⟨p, hp⟩ := exists_two_mul_inv_two_pow_lt _ h_sub
      use p, p
      have h_lt : q (i, p) + (2^p : ℚ)⁻¹ < r := by
        rw [← Rat.cast_lt (K := ℝ)]
        push_cast
        have h1 := hq_approx i p
        have h1' : (q (i, p) : ℝ) < v i + 2⁻¹ ^ p := sub_lt_iff_lt_add'.mp (abs_lt.mp h1).2
        have h_pow : (2⁻¹ : ℝ) ^ p = (2^p : ℝ)⁻¹ := by simp [inv_pow]
        rw [h_pow] at h1'
        linarith
      simp [h_lt, Option.mem_def]
    · intro h_dom
      rcases h_dom with ⟨p, a, hhp⟩
      simp only [Option.mem_def, Bool.cond_decide] at hhp
      split_ifs at hhp with h_lt
      have h_approx := hq_approx i p
      have h_pow : (2⁻¹ : ℝ) ^ p = (2^p : ℝ)⁻¹ := by simp [inv_pow]
      rw [h_pow] at h_approx
      have h_lt' : (q (i, p) : ℝ) + (2^p : ℝ)⁻¹ < (r : ℝ) := by
        have h2 : ((q (i, p) + (2^p : ℚ)⁻¹ : ℚ) : ℝ) < (r : ℝ) :=
          Rat.cast_lt.mpr (decide_eq_true_iff.mp h_lt)
        push_cast at h2
        exact h2
      have h_approx2 : -(2^p : ℝ)⁻¹ < (q (i, p) : ℝ) - v i := (abs_lt.mp h_approx).1
      linarith

/-- A strict lower comparison holds exactly when some rational approximation is separated. -/
private lemma rat_lt_iff_exists_separated_approx {α : Type*}
    (v : α → ℝ) (q : α × ℕ → ℚ)
    (hq_err : ∀ i p, |(q (i, p) : ℝ) - v i| < (2 : ℝ)⁻¹ ^ p)
    (iq : α × ℚ) :
    (iq.2 : ℝ) < v iq.1 ↔ ∃ p : ℕ, iq.2 + (2 : ℚ)⁻¹ ^ p < q (iq.1, p) := by
  constructor
  · intro h
    have h_sub : 0 < v iq.1 - (iq.2 : ℝ) := sub_pos.mpr h
    obtain ⟨p, hp⟩ := exists_two_mul_inv_two_pow_lt _ h_sub
    use p
    rw [← Rat.cast_lt (K := ℝ)]
    push_cast
    have h1 := hq_err iq.1 p
    have h1' : v iq.1 - (2:ℝ)⁻¹ ^ p < (q (iq.1, p) : ℝ) := by
      have h2 : -(2:ℝ)⁻¹ ^ p < (q (iq.1, p) : ℝ) - v iq.1 := (abs_lt.mp h1).1
      linarith
    have h_pow : (2^p : ℝ)⁻¹ = (2⁻¹ : ℝ) ^ p := by simp [inv_pow]
    rw [h_pow] at hp
    linarith
  · intro h
    rcases h with ⟨p, hp⟩
    have hp' : (iq.2 : ℝ) + (2:ℝ)⁻¹ ^ p < (q (iq.1, p) : ℝ) := by
      have : ((iq.2 + (2 : ℚ)⁻¹ ^ p : ℚ) : ℝ) < (q (iq.1, p) : ℝ) := Rat.cast_lt.mpr hp
      push_cast at this
      exact this
    have h1 := hq_err iq.1 p
    have h1' : (q (iq.1, p) : ℝ) < v iq.1 + (2:ℝ)⁻¹ ^ p := by
      have h2 : (q (iq.1, p) : ℝ) - v iq.1 < (2:ℝ)⁻¹ ^ p := (abs_lt.mp h1).2
      linarith
    linarith

/-- Searching for a rational approximation above a threshold is relatively enumerable. -/
private lemma isREIn_exists_separated_approx {α : Type*} [Primcodable α] (A : Set ℕ)
    (q : α × ℕ → ℚ) (hq : ComputableIn {charOracle A} q) :
    IsREIn A (fun iq : α × ℚ ↦ ∃ p : ℕ, iq.2 + (2 : ℚ)⁻¹ ^ p < q (iq.1, p)) := by
  let f : α × ℚ →. ℕ := fun iq ↦
    Nat.rfindOpt (fun p ↦ cond (decide (iq.2 + (2^p : ℚ)⁻¹ < q (iq.1, p))) (some p) none)
  have hf : PartrecIn {charOracle A} f := by
    apply PartrecIn.rfindOpt
    have hqArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ q (w.1.1, w.2)) :=
      hq.comp ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
    have hεArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ (2^w.2 : ℚ)⁻¹) :=
      computable_rat_inv_two_pow.computableIn.comp Computable.snd.computableIn
    have hrArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ w.1.2) :=
      (Computable.snd.comp Computable.fst).computableIn
    have hsum : ComputableIn {charOracle A}
        (fun w : (α × ℚ) × ℕ ↦ w.1.2 + (2^w.2 : ℚ)⁻¹) :=
      (Computable₂.computableIn₂ computable₂_ratAdd).comp hrArg hεArg
    have hcmp : ComputableIn {charOracle A}
        (fun w : (α × ℚ) × ℕ ↦ decide (w.1.2 + (2^w.2 : ℚ)⁻¹ < q (w.1.1, w.2))) :=
      (Computable₂.computableIn₂ computable₂_ratLt).comp hsum hqArg
    have hsome : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ some w.2) :=
      (Primrec.option_some.to_comp.comp Computable.snd).computableIn
    have hnone : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ (none : Option ℕ)) :=
      (Computable.const none).computableIn
    have H : ComputableIn {charOracle A}
        (fun (w : (α × ℚ) × ℕ) ↦
          cond (decide (w.1.2 + (2^w.2 : ℚ)⁻¹ < q (w.1.1, w.2))) (some w.2) none) :=
      computable_in_cond hcmp hsome hnone
    exact ComputableIn₂.mk H
  use f
  constructor
  · exact hf
  · intro ⟨i, r⟩
    simp only [f]
    rw [Nat.rfindOpt_dom]
    constructor
    · intro h
      rcases h with ⟨p, hp⟩
      use p, p
      have h_lt : r + (2^p : ℚ)⁻¹ < q (i, p) := by
        have h_pow : (2 : ℚ)⁻¹ ^ p = (2^p : ℚ)⁻¹ := by simp [inv_pow]
        rwa [← h_pow]
      simp [h_lt, Option.mem_def]
    · intro h_dom
      rcases h_dom with ⟨p, a, hhp⟩
      simp only [Option.mem_def, Bool.cond_decide] at hhp
      split_ifs at hhp with h_lt
      use p
      have h_pow : (2 : ℚ)⁻¹ ^ p = (2^p : ℚ)⁻¹ := by simp [inv_pow]
      rwa [h_pow]

/-- Strict rational lower comparisons with a uniform computable real family are also
enumerable. Blueprint node `metric:birkhoff`. -/
theorem birkhoff_computableIn_gt {α : Type*} [Primcodable α] (A : Set ℕ) (v : α → ℝ)
    (hv : IsComputableRealFamilyIn A v) :
    IsREIn A (fun iq : α × ℚ => (iq.2 : ℝ) < v iq.1) := by
  rcases hv with ⟨q, hq, hq_err⟩
  have h_equiv : (fun iq : α × ℚ ↦ (iq.2 : ℝ) < v iq.1) =
                 (fun iq : α × ℚ ↦ ∃ p : ℕ, iq.2 + (2 : ℚ)⁻¹ ^ p < q (iq.1, p)) := by
    funext iq
    exact propext (rat_lt_iff_exists_separated_approx v q hq_err iq)
  rw [h_equiv]
  exact isREIn_exists_separated_approx A q hq

end realFamilies

end Kolmogorov.PointToSet
