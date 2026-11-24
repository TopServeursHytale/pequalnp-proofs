import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2579.AlmostPureSide

/-- A three-point soundness certificate makes one side of the AND almost
contained in the neighborhood of the leaf context. -/
theorem one_side_at_most_one_exception
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) (A B : Finset (Fin n))
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (hcover : ∀ a ∈ A, ∀ b ∈ B, G.Adj u a ∨ G.Adj u b ∨ G.Adj a b) :
    (A.filter (fun a => ¬ G.Adj u a)).card ≤ 1 ∨
      (B.filter (fun b => ¬ G.Adj u b)).card ≤ 1 := by
  classical
  by_cases hA : (A.filter (fun a => ¬ G.Adj u a)).card ≤ 1
  · exact Or.inl hA
  · have hAlarge : 1 < (A.filter (fun a => ¬ G.Adj u a)).card := by omega
    obtain ⟨a, ha, a', ha', hne⟩ := Finset.one_lt_card.mp hAlarge
    obtain ⟨haA, hau⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha'A, ha'u⟩ := Finset.mem_filter.mp ha'
    have hsub : B.filter (fun b => ¬ G.Adj u b) ⊆
        Finset.univ.filter (fun b => G.Adj a b ∧ G.Adj a' b) := by
      intro b hb
      obtain ⟨hbB, hbu⟩ := Finset.mem_filter.mp hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact ((hcover a haA b hbB).resolve_left hau).resolve_left hbu
      · exact ((hcover a' ha'A b hbB).resolve_left ha'u).resolve_left hbu
    exact Or.inr ((Finset.card_le_card hsub).trans (h4 a a' hne))

/-- Every center adjacent to `v` and one selected distinct vertex is counted
by one of the common-neighbor sets, each of which has size at most one. -/
theorem centers_bound_by_selectors
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (v : Fin n) (T W : Finset (Fin n)) (hv : v ∉ T)
    (hW : ∀ u ∈ W, G.Adj u v ∧ ∃ t ∈ T, G.Adj u t) :
    W.card ≤ T.card := by
  classical
  let common := fun t : Fin n => Finset.univ.filter fun u => G.Adj v u ∧ G.Adj t u
  have hsub : W ⊆ T.biUnion common := by
    intro u hu
    obtain ⟨huv, t, ht, hut⟩ := hW u hu
    exact Finset.mem_biUnion.mpr
      ⟨t, ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, hut.symm⟩⟩
  calc
    W.card ≤ (T.biUnion common).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ T, (common t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, 1 := by
      apply Finset.sum_le_sum
      intro t ht
      exact h4 v t (by intro h; subst t; exact hv ht)
    _ = T.card := by simp

/-- A branch with three exposed leaves and one permitted bad leaf has at
most two possible centers once its singleton-operand vertex is fixed. -/
theorem almost_pure_centers_at_most_two
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (v : Fin n) (S W : Finset (Fin n)) (hv : v ∈ S) (hS : 3 ≤ S.card)
    (hW : ∀ u ∈ W, G.Adj u v ∧ (S.filter fun p => ¬ G.Adj u p).card ≤ 1) :
    W.card ≤ 2 := by
  classical
  have hlarge : 1 < (S.erase v).card := by
    rw [Finset.card_erase_of_mem hv]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlarge
  obtain ⟨hav, haS⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbv, hbS⟩ := Finset.mem_erase.mp hb
  have hcover : ∀ u ∈ W, G.Adj u v ∧ ∃ t ∈ ({a, b} : Finset (Fin n)), G.Adj u t := by
    intro u hu
    obtain ⟨huv, hbad⟩ := hW u hu
    refine ⟨huv, ?_⟩
    by_cases hua : G.Adj u a
    · exact ⟨a, by simp, hua⟩
    · have hub : G.Adj u b := by
        by_contra hub
        apply hab
        exact (Finset.card_le_one.mp hbad) a (Finset.mem_filter.mpr ⟨haS, hua⟩)
          b (Finset.mem_filter.mpr ⟨hbS, hub⟩)
      exact ⟨b, by simp, hub⟩
  have hcount := centers_bound_by_selectors n G h4 v {a, b} W
    (by simp [Ne.symm hav, Ne.symm hbv]) hcover
  exact hcount.trans (by simp [hab])

end PEqualNP.Outside.L_meta_2579.AlmostPureSide
