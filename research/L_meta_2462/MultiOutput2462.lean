import Mathlib
import PEqualNP.Defs

/-!
Work in progress for the multi-output child of L-meta-2462.
The combinatorial invariant uses only finsets, lists and labelled demands.
An entry records singleton support and the lines whose heavy complement input
is rejected. Missing wires are represented by `(∅, univ)`, i.e. constant false.
-/

namespace L2462Multi

variable {n : ℕ}

abbrev Entry (n : ℕ) := Finset (Fin n) × Finset (Fin n)

def zeroEntry : Entry n := (∅, Finset.univ)

def tagged (l : Fin n) (S : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  S.image fun p => (l, p)

@[simp] theorem mem_tagged (l : Fin n) (S : Finset (Fin n)) (e : Fin n × Fin n) :
    e ∈ tagged l S ↔ e.1 = l ∧ e.2 ∈ S := by
  rcases e with ⟨a, b⟩
  simp [tagged, Prod.mk.injEq, and_left_comm, eq_comm]

@[simp] theorem card_tagged (l : Fin n) (S : Finset (Fin n)) :
    (tagged l S).card = S.card := by
  apply Finset.card_image_of_injective
  intro p p' h
  exact congrArg Prod.snd h

def footprint (L : List (Entry n)) (W : Finset (Fin n × ℕ)) :
    Finset (Fin n × Fin n) :=
  W.biUnion fun r => tagged r.1 (L.getD r.2 zeroEntry).1

def Allowed (L : List (Entry n)) (W : Finset (Fin n × ℕ)) : Prop :=
  ∀ r ∈ W, r.1 ∈ (L.getD r.2 zeroEntry).2

def Count (t : ℕ) (L : List (Entry n)) : Prop :=
  ∀ W : Finset (Fin n × ℕ), Allowed L W → (footprint L W).card ≤ t + W.card

theorem getD_snoc_ne {α : Type} (L : List α) (v d : α) (j : ℕ)
    (h : j ≠ L.length) : (L ++ [v]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

@[simp] theorem getD_snoc_eq {α : Type} (L : List α) (v d : α) :
    (L ++ [v]).getD L.length d = v := by simp

theorem footprint_mono (L : List (Entry n)) {W V : Finset (Fin n × ℕ)}
    (h : W ⊆ V) : footprint L W ⊆ footprint L V := by
  intro e he
  obtain ⟨r, hr, her⟩ := Finset.mem_biUnion.mp he
  exact Finset.mem_biUnion.mpr ⟨r, h hr, her⟩

theorem footprint_card_le (L : List (Entry n)) (W : Finset (Fin n × ℕ))
    (hsmall : ∀ r ∈ W, (L.getD r.2 zeroEntry).1.card ≤ 1) :
    (footprint L W).card ≤ W.card := by
  apply le_trans Finset.card_biUnion_le
  calc
    ∑ r ∈ W, (tagged r.1 (L.getD r.2 zeroEntry).1).card
        ≤ ∑ _r ∈ W, 1 := by
          apply Finset.sum_le_sum
          intro r hr
          simpa using hsmall r hr
    _ = W.card := by simp

def Valid (I : Fin n → Fin n → Prop) (e : Entry n) : Prop :=
  ∀ p ∈ e.1, ∀ l ∈ e.2, I p l

def NoRectangle (I : Fin n → Fin n → Prop) : Prop :=
  ∀ p p' l l', p ≠ p' → I p l → I p' l → I p l' → I p' l' → l = l'

theorem large_pure_unique {I : Fin n → Fin n → Prop} {e : Entry n}
    (hI : NoRectangle I) (hv : Valid I e) (hlarge : 1 < e.1.card)
    {l l' : Fin n} (hl : l ∈ e.2) (hl' : l' ∈ e.2) : l = l' := by
  obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp hlarge
  exact hI p p' l l' hne (hv p hp l hl) (hv p' hp' l hl)
    (hv p hp l' hl') (hv p' hp' l' hl')

/- `local` gives at most two old demands covering a new demand.  This is
   immediate at OR gates. At an AND gate, choose one child rejecting the
   heavy input, which alone covers the entire singleton support. -/
theorem count_snoc (t : ℕ) (L : List (Entry n)) (e : Entry n)
    (hc : Count t L)
    (hunique : ∀ l l', l ∈ e.2 → l' ∈ e.2 → 1 < e.1.card → l = l')
    (hlocal : ∀ l ∈ e.2, 1 < e.1.card →
      ∃ A : Finset ℕ, A.card ≤ 2 ∧
        (∀ a ∈ A, l ∈ (L.getD a zeroEntry).2) ∧
        e.1 ⊆ A.biUnion (fun a => (L.getD a zeroEntry).1)) :
    Count (t + 1) (L ++ [e]) := by
  intro W hW
  by_cases hsmall : e.1.card ≤ 1
  · let Wold := W.filter fun r => r.2 ≠ L.length
    let Wnew := W.filter fun r => r.2 = L.length
    have hold : Allowed L Wold := by
      intro r hr
      obtain ⟨hrW, hrne⟩ := Finset.mem_filter.mp hr
      have h := hW r hrW
      rw [getD_snoc_ne _ _ _ _ hrne] at h
      exact h
    have hcover : footprint (L ++ [e]) W ⊆
        footprint L Wold ∪ footprint (L ++ [e]) Wnew := by
      intro a ha
      obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp ha
      by_cases hrj : r.2 = L.length
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr
          ⟨r, Finset.mem_filter.mpr ⟨hr, hrj⟩, har⟩
      · apply Finset.mem_union_left
        rw [getD_snoc_ne _ _ _ _ hrj] at har
        exact Finset.mem_biUnion.mpr
          ⟨r, Finset.mem_filter.mpr ⟨hr, hrj⟩, har⟩
    have hnew : (footprint (L ++ [e]) Wnew).card ≤ Wnew.card := by
      apply footprint_card_le
      intro r hr
      have hrj := (Finset.mem_filter.mp hr).2
      simpa [hrj] using hsmall
    have hpart : Wold.card + Wnew.card = W.card := by
      simpa [Wold, Wnew] using
        (Finset.card_filter_add_card_filter_not (s := W) (fun r => r.2 ≠ L.length))
    have hcount := hc Wold hold
    have hcard := le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
    omega
  · have hlarge : 1 < e.1.card := by omega
    by_cases hnew : ∃ r ∈ W, r.2 = L.length
    · obtain ⟨r0, hr0, hr0j⟩ := hnew
      have hpure : r0.1 ∈ e.2 := by
        have h := hW r0 hr0
        simpa [hr0j] using h
      obtain ⟨A, hAcard, hApure, hAcovers⟩ := hlocal r0.1 hpure hlarge
      let V := A.image fun a => (r0.1, a)
      let W' := W.erase r0 ∪ V
      have hother : ∀ r ∈ W, r ≠ r0 → r.2 ≠ L.length := by
        intro r hr hrne hrj
        have hp : r.1 ∈ e.2 := by
          have h := hW r hr
          simpa [hrj] using h
        have hline := hunique r.1 r0.1 hp hpure hlarge
        apply hrne
        exact Prod.ext hline (hrj.trans hr0j.symm)
      have hallowed : Allowed L W' := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · obtain ⟨hrne, hrW⟩ := Finset.mem_erase.mp hr
          have h := hW r hrW
          rw [getD_snoc_ne _ _ _ _ (hother r hrW hrne)] at h
          exact h
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
          exact hApure a ha
      have hcover : footprint (L ++ [e]) W ⊆ footprint L W' := by
        intro a ha
        obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp ha
        by_cases hre : r = r0
        · subst r
          have har' : a.1 = r0.1 ∧ a.2 ∈ e.1 := by
            simpa [hr0j] using har
          obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp (hAcovers har'.2)
          refine Finset.mem_biUnion.mpr ⟨(r0.1, j), ?_, ?_⟩
          · apply Finset.mem_union_right
            exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
          · exact (mem_tagged _ _ _).mpr ⟨har'.1, haj⟩
        · rw [getD_snoc_ne _ _ _ _ (hother r hr hre)] at har
          exact Finset.mem_biUnion.mpr
            ⟨r, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hre, hr⟩), har⟩
      have hV : V.card ≤ 2 := le_trans Finset.card_image_le hAcard
      have hsize : W'.card ≤ W.card - 1 + 2 := by
        have hu := Finset.card_union_le (W.erase r0) V
        rw [Finset.card_erase_of_mem hr0] at hu
        exact le_trans hu (Nat.add_le_add_left hV _)
      have hpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨r0, hr0⟩
      have hcount := hc W' hallowed
      have hsub := Finset.card_le_card hcover
      omega
    · have heq : footprint (L ++ [e]) W = footprint L W := by
        apply Finset.biUnion_congr rfl
        intro r hr
        rw [getD_snoc_ne _ _ _ _ (fun hj => hnew ⟨r, hr, hj⟩)]
      have hold : Allowed L W := by
        intro r hr
        have h := hW r hr
        rw [getD_snoc_ne _ _ _ _ (fun hj => hnew ⟨r, hr, hj⟩)] at h
        exact h
      rw [heq]
      have hcount := hc W hold
      omega

def joinEntry (L : List (Entry n)) (ins : List ℕ) : Entry n :=
  (ins.toFinset.biUnion (fun a => (L.getD a zeroEntry).1),
    Finset.univ.filter fun l => ∀ a ∈ ins.toFinset, l ∈ (L.getD a zeroEntry).2)

def meetEntry (L : List (Entry n)) (ins : List ℕ) : Entry n :=
  (Finset.univ.filter (fun p => ∀ a ∈ ins.toFinset, p ∈ (L.getD a zeroEntry).1),
    ins.toFinset.biUnion fun a => (L.getD a zeroEntry).2)

def Good (I : Fin n → Fin n → Prop) (L : List (Entry n)) : Prop :=
  ∀ w, Valid I (L.getD w zeroEntry)

theorem valid_join {I : Fin n → Fin n → Prop} (L : List (Entry n)) (ins : List ℕ)
    (h : Good I L) : Valid I (joinEntry L ins) := by
  intro p hp l hl
  obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.mp hp
  have hla := (Finset.mem_filter.mp hl).2 a ha
  exact h a p hpa l hla

theorem valid_meet {I : Fin n → Fin n → Prop} (L : List (Entry n)) (ins : List ℕ)
    (h : Good I L) : Valid I (meetEntry L ins) := by
  intro p hp l hl
  obtain ⟨a, ha, hla⟩ := Finset.mem_biUnion.mp hl
  have hpa := (Finset.mem_filter.mp hp).2 a ha
  exact h a p hpa l hla

theorem good_snoc {I : Fin n → Fin n → Prop} (L : List (Entry n)) (e : Entry n)
    (h : Good I L) (he : Valid I e) : Good I (L ++ [e]) := by
  intro w
  by_cases hw : w = L.length
  · simpa [hw] using he
  · rw [getD_snoc_ne _ _ _ _ hw]
    exact h w

theorem count_join {I : Fin n → Fin n → Prop} (t : ℕ) (L : List (Entry n))
    (ins : List ℕ) (hlen : ins.length ≤ 2) (hI : NoRectangle I)
    (hg : Good I L) (hc : Count t L) :
    Count (t + 1) (L ++ [joinEntry L ins]) := by
  apply count_snoc t L _ hc
  · intro l l' hl hl' hlarge
    exact large_pure_unique hI (valid_join L ins hg) hlarge hl hl'
  · intro l hl _
    refine ⟨ins.toFinset, le_trans (List.toFinset_card_le _) hlen, ?_, ?_⟩
    · exact (Finset.mem_filter.mp hl).2
    · exact Finset.Subset.refl _

theorem count_meet {I : Fin n → Fin n → Prop} (t : ℕ) (L : List (Entry n))
    (ins : List ℕ) (hI : NoRectangle I) (hg : Good I L) (hc : Count t L) :
    Count (t + 1) (L ++ [meetEntry L ins]) := by
  apply count_snoc t L _ hc
  · intro l l' hl hl' hlarge
    exact large_pure_unique hI (valid_meet L ins hg) hlarge hl hl'
  · intro l hl _
    obtain ⟨a, ha, hla⟩ := Finset.mem_biUnion.mp hl
    refine ⟨{a}, by simp, ?_, ?_⟩
    · intro b hb
      simpa only [Finset.mem_singleton.mp hb] using hla
    · intro p hp
      simpa using (Finset.mem_filter.mp hp).2 a ha

open PEqualNP.CircuitLowerBounds

def gateEntry (L : List (Entry n)) (g : Gate) : Entry n :=
  match g.op with
  | .or => joinEntry L g.inputs
  | .and => meetEntry L g.inputs
  | _ => zeroEntry

def entriesFrom (gs : List Gate) (L : List (Entry n)) : List (Entry n) :=
  gs.foldl (fun L g => L ++ [gateEntry L g]) L

def GateOK (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

theorem count_good_step {I : Fin n → Fin n → Prop} (t : ℕ)
    (L : List (Entry n)) (g : Gate) (hok : GateOK g) (hI : NoRectangle I)
    (hg : Good I L) (hc : Count t L) :
    Good I (L ++ [gateEntry L g]) ∧ Count (t + 1) (L ++ [gateEntry L g]) := by
  rcases hok with ⟨hop, hlen⟩
  rcases hop with hop | hop
  · simp only [gateEntry, hop]
    exact ⟨good_snoc L _ hg (valid_meet L g.inputs hg),
      count_meet t L g.inputs hI hg hc⟩
  · simp only [gateEntry, hop]
    exact ⟨good_snoc L _ hg (valid_join L g.inputs hg),
      count_join t L g.inputs hlen hI hg hc⟩

theorem count_good_from {I : Fin n → Fin n → Prop} (gs : List Gate)
    (hI : NoRectangle I) : ∀ (t : ℕ) (L : List (Entry n)),
    (∀ g ∈ gs, GateOK g) → Good I L → Count t L →
      Good I (entriesFrom gs L) ∧ Count (t + gs.length) (entriesFrom gs L) := by
  induction gs with
  | nil => intro t L _ hg hc; exact ⟨hg, hc⟩
  | cons g gs ih =>
    intro t L hok hg hc
    have hstep := count_good_step t L g (hok g List.mem_cons_self) hI hg hc
    have htail := ih (t + 1) (L ++ [gateEntry L g])
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hstep.1 hstep.2
    simpa only [entriesFrom, List.foldl_cons, List.length_cons,
      show t + (gs.length + 1) = t + 1 + gs.length by omega] using htail

def inputEntries (I : Fin n → Fin n → Prop) [DecidableRel I] : List (Entry n) :=
  List.ofFn fun p : Fin n => ({p}, Finset.univ.filter fun l => I p l)

theorem good_inputs (I : Fin n → Fin n → Prop) [DecidableRel I] :
    Good I (inputEntries I) := by
  intro w p hp l hl
  by_cases hw : w < n
  · have hp' : p = (⟨w, hw⟩ : Fin n) := by simpa [inputEntries, hw] using hp
    subst p
    simpa [inputEntries, hw] using hl
  · have hz : (inputEntries I).getD w zeroEntry = zeroEntry :=
      List.getD_eq_default _ _ (by simp [inputEntries]; omega)
    rw [hz] at hp
    simp [zeroEntry] at hp

theorem count_inputs (I : Fin n → Fin n → Prop) [DecidableRel I] :
    Count 0 (inputEntries I) := by
  intro W _
  rw [zero_add]
  apply footprint_card_le
  intro r _
  by_cases hw : r.2 < n
  · simp [inputEntries, hw]
  · rw [List.getD_eq_default _ _ (by simp [inputEntries]; omega)]
    simp [zeroEntry]

theorem count_entries (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hI : NoRectangle I) (gs : List Gate) (hok : ∀ g ∈ gs, GateOK g) :
    Count gs.length (entriesFrom gs (inputEntries I)) := by
  simpa using (count_good_from gs hI 0 (inputEntries I) hok
    (good_inputs I) (count_inputs I)).2

end L2462Multi


-- Semantic layer to append after MultiOutput.lean for a combined compilation.
-- This fragment deliberately leaves the algebraic file untouched.

namespace L2462Multi

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

def singleInput (p : Fin n) : Fin n → Bool := fun p' => decide (p' = p)

def heavyInput (I : Fin n → Fin n → Prop) [DecidableRel I]
    (l : Fin n) : Fin n → Bool := fun p => decide (¬ I p l)

def boolWiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Tracks (L : List (Entry n)) (S T : Fin n → List Bool) : Prop :=
  (∀ p, (S p).length = L.length) ∧
  (∀ l, (T l).length = L.length) ∧
  (∀ w p, p ∈ (L.getD w zeroEntry).1 ↔ (S p).getD w false = true) ∧
  (∀ w l, l ∈ (L.getD w zeroEntry).2 ↔ (T l).getD w false = false)

theorem gateEntry_single_iff (L : List (Entry n)) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (p : Fin n) (w : List Bool)
    (h : ∀ i, p ∈ (L.getD i zeroEntry).1 ↔ w.getD i false = true) :
    p ∈ (gateEntry L g).1 ↔
      g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
  simp only [List.getD_eq_getElem?_getD] at h
  rcases hop with hop | hop
  · simp [gateEntry, hop, meetEntry, GateOp.eval, h]
  · simp [gateEntry, hop, joinEntry, GateOp.eval, h]

theorem gateEntry_reject_iff (L : List (Entry n)) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (l : Fin n) (w : List Bool)
    (h : ∀ i, l ∈ (L.getD i zeroEntry).2 ↔ w.getD i false = false) :
    l ∈ (gateEntry L g).2 ↔
      g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
  simp only [List.getD_eq_getElem?_getD] at h
  rcases hop with hop | hop
  · simp [gateEntry, hop, meetEntry, GateOp.eval, h]
  · simp [gateEntry, hop, joinEntry, GateOp.eval, h]

theorem tracks_step (L : List (Entry n)) (S T : Fin n → List Bool)
    (g : Gate) (hop : g.op = .and ∨ g.op = .or) (h : Tracks L S T) :
    Tracks (L ++ [gateEntry L g])
      (fun p => S p ++ [g.op.eval (g.inputs.map fun i => (S p).getD i false)])
      (fun l => T l ++ [g.op.eval (g.inputs.map fun i => (T l).getD i false)]) := by
  obtain ⟨hSl, hTl, hS, hT⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    simp [hSl p]
  · intro l
    simp [hTl l]
  · intro w p
    by_cases hw : w = L.length
    · subst w
      rw [getD_snoc_eq, ← hSl p, getD_snoc_eq]
      exact gateEntry_single_iff L g hop p (S p) (fun i => hS i p)
    · rw [getD_snoc_ne L _ _ w hw,
        getD_snoc_ne (S p) _ _ w (by simpa [hSl p] using hw)]
      exact hS w p
  · intro w l
    by_cases hw : w = L.length
    · subst w
      rw [getD_snoc_eq, ← hTl l, getD_snoc_eq]
      exact gateEntry_reject_iff L g hop l (T l) (fun i => hT i l)
    · rw [getD_snoc_ne L _ _ w hw,
        getD_snoc_ne (T l) _ _ w (by simpa [hTl l] using hw)]
      exact hT w l

theorem tracks_from (gs : List Gate) :
    ∀ (L : List (Entry n)) (S T : Fin n → List Bool),
      (∀ g ∈ gs, GateOK g) → Tracks L S T →
      Tracks (entriesFrom gs L)
        (fun p => boolWiresFrom gs (S p)) (fun l => boolWiresFrom gs (T l)) := by
  induction gs with
  | nil => intro L S T _ h; exact h
  | cons g gs ih =>
    intro L S T hok h
    have hstep := tracks_step L S T g (hok g List.mem_cons_self).1 h
    have htail := ih (L ++ [gateEntry L g])
      (fun p => S p ++ [g.op.eval (g.inputs.map fun i => (S p).getD i false)])
      (fun l => T l ++ [g.op.eval (g.inputs.map fun i => (T l).getD i false)])
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hstep
    simpa only [entriesFrom, boolWiresFrom, List.foldl_cons] using htail

theorem tracks_inputs (I : Fin n → Fin n → Prop) [DecidableRel I] :
    Tracks (inputEntries I) (fun p => List.ofFn (singleInput p))
      (fun l => List.ofFn (heavyInput I l)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    simp [inputEntries]
  · intro l
    simp [inputEntries]
  · intro w p
    by_cases hw : w < n
    · simp [inputEntries, singleInput, hw, eq_comm]
    · rw [List.getD_eq_default _ _ (by simp [inputEntries]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      simp [zeroEntry]
  · intro w l
    by_cases hw : w < n
    · simp [inputEntries, heavyInput, hw]
    · rw [List.getD_eq_default _ _ (by simp [inputEntries]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      simp [zeroEntry]

theorem entries_single_iff (I : Fin n → Fin n → Prop) [DecidableRel I]
    (D : Circuit) (hok : ∀ g ∈ D.gates, GateOK g) (w : ℕ) (p : Fin n) :
    p ∈ ((entriesFrom D.gates (inputEntries I)).getD w zeroEntry).1 ↔
      circuitFun n { D with output := w } (singleInput p) = true := by
  have h := tracks_from D.gates (inputEntries I)
    (fun p => List.ofFn (singleInput p))
    (fun l => List.ofFn (heavyInput I l)) hok (tracks_inputs I)
  simpa only [boolWiresFrom, circuitFun, Circuit.eval, Circuit.wires] using h.2.2.1 w p

theorem entries_reject_iff (I : Fin n → Fin n → Prop) [DecidableRel I]
    (D : Circuit) (hok : ∀ g ∈ D.gates, GateOK g) (w : ℕ) (l : Fin n) :
    l ∈ ((entriesFrom D.gates (inputEntries I)).getD w zeroEntry).2 ↔
      circuitFun n { D with output := w } (heavyInput I l) = false := by
  have h := tracks_from D.gates (inputEntries I)
    (fun p => List.ofFn (singleInput p))
    (fun l => List.ofFn (heavyInput I l)) hok (tracks_inputs I)
  simpa only [boolWiresFrom, circuitFun, Circuit.eval, Circuit.wires] using h.2.2.2 w l

theorem output_rejects_heavy (I : Fin n → Fin n → Prop) [DecidableRel I]
    (D : Circuit) (o : Fin n → ℕ)
    (hdom : ∀ (l : Fin n) (x : Fin n → Bool),
      circuitFun n { D with output := o l } x = true →
        ∃ p : Fin n, I p l ∧ x p = true) (l : Fin n) :
    circuitFun n { D with output := o l } (heavyInput I l) = false := by
  cases hv : circuitFun n { D with output := o l } (heavyInput I l) with
  | false => rfl
  | true =>
    obtain ⟨p, hip, hp⟩ := hdom l (heavyInput I l) hv
    have hn : ¬ I p l := by simpa [heavyInput] using hp
    exact False.elim (hn hip)

theorem multi_output_bound (I : Fin n → Fin n → Prop) [DecidableRel I]
    (D : Circuit) (o : Fin n → ℕ)
    (hI : NoRectangle I) (hok : ∀ g ∈ D.gates, GateOK g)
    (hdom : ∀ (l : Fin n) (x : Fin n → Bool),
      circuitFun n { D with output := o l } x = true →
        ∃ p : Fin n, I p l ∧ x p = true) :
    Fintype.card { e : Fin n × Fin n //
      circuitFun n { D with output := o e.2 } (singleInput e.1) = true } ≤
      D.size + Fintype.card { l : Fin n // ∃ p : Fin n,
        circuitFun n { D with output := o l } (singleInput p) = true } := by
  classical
  let L := entriesFrom D.gates (inputEntries I)
  let active : Finset (Fin n) := Finset.univ.filter fun l => ∃ p : Fin n,
    circuitFun n { D with output := o l } (singleInput p) = true
  let W : Finset (Fin n × ℕ) := active.image fun l => (l, o l)
  have hallowed : Allowed L W := by
    intro r hr
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hr
    exact (entries_reject_iff I D hok (o l) l).mpr (output_rejects_heavy I D o hdom l)
  have hWcard : W.card = active.card := by
    apply Finset.card_image_of_injective
    intro l l' h
    exact congrArg Prod.fst h
  have hcount : (footprint L W).card ≤ D.size + active.card := by
    have h := count_entries I hI D.gates hok W hallowed
    simpa only [L, hWcard, Circuit.size] using h
  let lift :
      { e : Fin n × Fin n //
        circuitFun n { D with output := o e.2 } (singleInput e.1) = true } →
      ↑(footprint L W) := fun e => ⟨(e.val.2, e.val.1), by
        apply Finset.mem_biUnion.mpr
        refine ⟨(e.val.2, o e.val.2), ?_, ?_⟩
        · apply Finset.mem_image.mpr
          refine ⟨e.val.2, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.val.1, e.property⟩
        · apply (mem_tagged _ _ _).mpr
          exact ⟨rfl, (entries_single_iff I D hok (o e.val.2) e.val.1).mpr e.property⟩⟩
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hsupport :
      Fintype.card { e : Fin n × Fin n //
        circuitFun n { D with output := o e.2 } (singleInput e.1) = true } ≤
      (footprint L W).card := by
    simpa using Fintype.card_le_of_injective lift hinj
  have hactive : active.card = Fintype.card { l : Fin n // ∃ p : Fin n,
      circuitFun n { D with output := o l } (singleInput p) = true } := by
    rw [Fintype.card_subtype]
  exact hsupport.trans (hcount.trans_eq (congrArg (D.size + ·) hactive))

theorem multi_output_bound_of_unique (I : Fin n → Fin n → Prop) [DecidableRel I]
    (D : Circuit) (o : Fin n → ℕ)
    (hunique : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    (hok : ∀ g ∈ D.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hdom : ∀ (l : Fin n) (x : Fin n → Bool),
      circuitFun n { D with output := o l } x = true →
        ∃ p : Fin n, I p l ∧ x p = true) :
    Fintype.card { e : Fin n × Fin n //
      circuitFun n { D with output := o e.2 } (fun p' => decide (p' = e.1)) = true } ≤
      D.size + Fintype.card { l : Fin n // ∃ p : Fin n,
        circuitFun n { D with output := o l } (fun p' => decide (p' = p)) = true } := by
  apply multi_output_bound I D o ?_ hok hdom
  intro p p' l l' hne hpl hp'l hpl' hp'l'
  obtain ⟨l₀, _, hu⟩ := hunique p p' hne
  exact (hu l ⟨hpl, hp'l⟩).trans (hu l' ⟨hpl', hp'l'⟩).symm

end L2462Multi
