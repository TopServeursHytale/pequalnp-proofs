import Mathlib
import PEqualNP.Defs

namespace Research2658

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2


lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

open PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

lemma and_false_on_independent {n : ℕ} (G : SimpleGraph (Fin n)) (u0 : Fin n)
    (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hlen : (gateAt C j).inputs.length ≤ 2)
    (hp : ∀ u v : Fin n,
      val C (List.ofFn (pairInput u v)) (n+j) = true → G.Adj u v)
    (x : Fin n → Bool)
    (hx : ∀ u v : Fin n, x u = true → x v = true → ¬ G.Adj u v)
    (hs : ∀ w < n+j, val C (List.ofFn x) w = true →
      ∃ u : Fin n, x u = true ∧
        ∀ y : Fin n → Bool, y u = true → val C (List.ofFn y) w = true) :
    val C (List.ofFn x) (n+j) ≠ true := by
  intro hv
  have reads := (val_and (by simp) hj hop).mp hv
  cases hi : (gateAt C j).inputs with
  | nil =>
    have ht : val C (List.ofFn (pairInput u0 u0)) (n+j) = true := by
      apply (val_and (by simp) hj hop).mpr
      intro w hw
      simp only [hi, List.not_mem_nil] at hw
    exact G.irrefl (hp u0 u0 ht)
  | cons a tail =>
    have ha := reads a (by simp [hi])
    obtain ⟨u, hu, hdu⟩ := hs a ha.1 ha.2
    cases ht : tail with
    | nil =>
      have huv : val C (List.ofFn (pairInput u u)) (n+j) = true := by
        apply (val_and (by simp) hj hop).mpr
        intro w hw
        simp only [hi, ht, List.mem_singleton] at hw
        subst w
        exact ⟨ha.1, hdu _ (by simp [pairInput])⟩
      exact G.irrefl (hp u u huv)
    | cons b rest =>
      have hb := reads b (by simp [hi, ht])
      obtain ⟨v, hv, hdv⟩ := hs b hb.1 hb.2
      have hr : rest = [] := by
        have hlen' : rest.length + 1 + 1 ≤ 2 := by
          simpa only [hi, ht, List.length_cons] using hlen
        have : rest.length = 0 := by omega
        exact List.length_eq_zero_iff.mp this
      have huv : val C (List.ofFn (pairInput u v)) (n+j) = true := by
        apply (val_and (by simp) hj hop).mpr
        intro w hw
        simp only [hi, ht, hr, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨ha.1, hdu _ (by simp [pairInput])⟩
        · exact ⟨hb.1, hdv _ (by simp [pairInput])⟩
      exact hx u v hu hv (hp u v huv)

lemma pair_clean_suffices {n : ℕ} (G : SimpleGraph (Fin n))
    (u0 : Fin n) (C : Circuit) (hM : Monotone2 C)
    (hp : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, val C (List.ofFn (pairInput u v)) (n+j) = true → G.Adj u v) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ x : Fin n → Bool, val C (List.ofFn x) (n+j) = true →
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  intro j hj hand x hv
  by_contra hbad
  have independent : ∀ u v : Fin n, x u = true → x v = true → ¬ G.Adj u v := by
    intro u v hu hv he
    exact hbad ⟨u,v,he,hu,hv⟩
  have trace : ∀ w : ℕ, val C (List.ofFn x) w = true →
      ∃ u : Fin n, x u = true ∧
        ∀ y : Fin n → Bool, y u = true → val C (List.ofFn y) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hinput : w < n
      · refine ⟨⟨w,hinput⟩, ?_, ?_⟩
        · exact (val_ofFn C x ⟨w,hinput⟩).symm.trans hw
        · intro y hy
          exact (val_ofFn C y ⟨w,hinput⟩).trans hy
      · by_cases hlast : n + C.gates.length ≤ w
        · have hfalse := val_ge (C := C) (x := List.ofFn x) (n := n) (by simp) hlast
          rw [hfalse] at hw
          cases hw
        · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n, by omega⟩
          have hk : k < C.gates.length := by omega
          have hmk := hM (gateAt C k) (gateAt_mem hk)
          have hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmk.1
          rcases hop with hand | hor
          · exact False.elim (and_false_on_independent G u0 C k hk hand hmk.2
              (hp k hk hand) x independent ih hw)
          · obtain ⟨a,ha,hlt,hva⟩ := (val_or (by simp) hk hor).mp hw
            obtain ⟨u,hu,hdom⟩ := ih a hlt hva
            refine ⟨u,hu,?_⟩
            intro y hy
            exact (val_or (by simp) hk hor).mpr ⟨a,ha,hlt,hdom y hy⟩
  exact and_false_on_independent G u0 C j hj hand
    (hM (gateAt C j) (gateAt_mem hj)).2 (hp j hj hand) x independent
    (fun w _ => trace w) hv

/-- Exact interface of the first proposed child of PR 5758.  This implication
does not require the graph to be C4-free, nor any hypothesis on the output. -/
theorem pair_clean_suffices_getD (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
    (hn : 0 < n) (hM : Monotone2 C)
    (hp : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      g.op = GateOp.and → ∀ u v : Fin n, ¬ G.Adj u v →
      (C.wires (List.ofFn (pairInput u v))).getD (n+j) false = false) :
    ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      g.op = GateOp.and → ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n+j) false = true →
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  have hp' : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, val C (List.ofFn (pairInput u v)) (n+j) = true → G.Adj u v := by
    intro j hj hand u v hv
    by_contra hnedge
    have hjg : C.gates[j]? = some (gateAt C j) := by
      rw [gateAt_eq hj]
      exact List.getElem?_eq_getElem hj
    have hf := hp j (gateAt C j) hjg hand u v hnedge
    change val C (List.ofFn (pairInput u v)) (n+j) = false at hf
    rw [hf] at hv
    cases hv
  intro j g hget hand x hv
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hget
  have hg : gateAt C j = g := (gateAt_eq hj).trans hgj
  exact pair_clean_suffices G ⟨0,hn⟩ C hM hp' j hj (hg ▸ hand) x hv

end Research2658

