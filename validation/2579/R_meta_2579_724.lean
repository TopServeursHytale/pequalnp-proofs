import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Split the residual by the two operand routes of a top AND gate.
-- Coverage proof adapted from RobertCass's L_meta_1766, upstream PR 4025.
-- Source commit: 648ed26b7255fc04a9a30f8380bb501f83e96f89.
-- Its definitions and lemmas are local to this proof, with no additional declarations.

theorem PEqualNP.Outside.R_meta_2579_724 :
  (∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
    let R := ((Ustar G C).filter (fun e => ¬ ∃ u v : Fin n, e = s(u,v) ∧
      ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n+h)).card ∧
        (∀ w ∈ orIn n C (n+h), G.Adj u w) ∧ orIn n C (opnd C h b) = {v}))
    (R.filter (fun e => ∃ u v : Fin n, e = s(u,v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1-b)) h ∧
        gateVal n C h (pairInput u v) = true)).card ≤ k * (C.size + 1)) →
  (∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
    let R := ((Ustar G C).filter (fun e => ¬ ∃ u v : Fin n, e = s(u,v) ∧
      ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n+h)).card ∧
        (∀ w ∈ orIn n C (n+h), G.Adj u w) ∧ orIn n C (opnd C h b) = {v}))
    (R.filter (fun e => ∃ u v : Fin n, e = s(u,v) ∧
      ∃ a ∈ tops G C, ∃ h ∈ junk G C, ∃ h' ∈ junk G C,
        h ≠ h' ∧ OrReaches n C (opnd C a 0) h ∧ OrReaches n C (opnd C a 1) h' ∧
        gateVal n C h (pairInput u v) = true ∧ gateVal n C h' (pairInput u v) = true)).card ≤ k * (C.size + 1)) →
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  intro leafBound doubleBound
  classical
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp (config := { congrConsts := false })
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp (config := { congrConsts := false }) [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp (config := { congrConsts := false }) only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp (config := { congrConsts := false }) [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp (config := { congrConsts := false }) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp (config := { congrConsts := false }) [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp (config := { congrConsts := false }) at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp (config := { congrConsts := false }) [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp (config := { congrConsts := false }) only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp (config := { congrConsts := false }) [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp (config := { congrConsts := false }) [stepWire]; omega)]
          simp (config := { congrConsts := false }) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa (config := { congrConsts := false }) using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp (config := { congrConsts := false }) [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp (config := { congrConsts := false }) only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    dsimp only [gateAt]
    simp (config := { congrConsts := false }) [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have opMono_imp : OpMono (fun a b => a = true → b = true) := by
    intro op hop l f g h
    rcases hop with rfl | rfl
    · dsimp only [GateOp.eval]
      simp (config := { congrConsts := false }) only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro h1 i hi; exact h i hi (h1 i hi)
    · dsimp only [GateOp.eval]
      simp (config := { congrConsts := false }) only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    dsimp only [GateOp.eval]
    simp (config := { congrConsts := false }) only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

  have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
      val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    dsimp only [GateOp.eval]
    simp (config := { congrConsts := false }) only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2

  have biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
      (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
      (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
      A.card ≤ 1 ∨ B.card ≤ 1 := by
    by_contra hcon
    simp (config := { congrConsts := false }) only [not_or, not_le] at hcon
    obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
    obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
    exact h4 a b c d hac hbd
      ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

  have val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
      val C (List.ofFn x) u.val = x u := by
    rw [val_input (n := n) (by simp (config := { congrConsts := false })) u.isLt]
    simp (config := { congrConsts := false }) [List.getD_eq_getElem?_getD]

  have gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
      PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

  let OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
    ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      w' ∈ (gateAt C k).inputs ∧ w' < n + k

  have orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
      val C x w = true := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head hstep _ ih =>
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

  have or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
      ∀ w : ℕ, val C x w = true →
        ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
          (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hv
      by_cases hw : w < n
      · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
      · by_cases hlen : n + C.gates.length ≤ w
        · rw [val_ge hx hlen] at hv; cases hv
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < C.gates.length := by omega
          by_cases hop : (gateAt C k).op = GateOp.or
          · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
            obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
            exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
          · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

  have pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
    dsimp only [pairInput]
    simp (config := { congrConsts := false })

  have pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
    dsimp only [pairInput]
    simp (config := { congrConsts := false })

  have pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
    dsimp only [pairInput]
    simp (config := { congrConsts := false })

  have graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
      graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    dsimp only [graphFun]
    simp (config := { congrConsts := false }) only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq, pairInput_true]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (G.irrefl hab).elim
      · exact hab
      · exact hab.symm
      · exact (G.irrefl hab).elim
    · intro h
      exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

  have operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
      (hv : val C (List.ofFn (pairInput u v)) p = true) :
      (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
      (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
        Relation.ReflTransGen (OrStep n C) p (n + h) ∧
        val C (List.ofFn (pairInput u v)) (n + h) = true) := by
    obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
      (by simp (config := { congrConsts := false })) p hv
    rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
    · left
      refine ⟨⟨w', hlt⟩, ?_, hr⟩
      have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
      rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
      exact (pairInput_true u v _).mp h1.symm
    · right
      exact ⟨h, hh, hop, hr, hv'⟩

  have reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
      (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
      val C (List.ofFn x) p = true :=
    orStep_up (n := n) (by simp (config := { congrConsts := false })) hr (by rw [val_ofFn]; exact ht)

  have side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
      (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
      (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
      (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
      (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
      (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
      (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
    apply hF
    apply hbel
    rw [val_and (n := n) (by simp (config := { congrConsts := false })) ha hop, hin]
    intro i hi
    simp (config := { congrConsts := false }) only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
    · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

  have edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
      (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
      (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
      (u v : Fin n) (huv : F (pairInput u v) = true) :
      ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
        Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
        val C (List.ofFn (pairInput u v)) (n + a) = true := by
    rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
      ⟨t, _, hr⟩ | h
    · exfalso
      have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
      rw [hout] at h1
      exact G.irrefl (hF t t h1)
    · exact h

  have below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
      (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
      (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
      (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
    rw [← hout]
    exact orStep_up (n := n) (by simp (config := { congrConsts := false })) hr hv


  have cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp (config := { congrConsts := false })
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      dsimp only [coneStep]
      simp (config := { congrConsts := false })
      omega

  have cones_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp (config := { congrConsts := false })
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
        rw [cones_len]; simp (config := { congrConsts := false })
      have key : ∀ k, k < gs.length →
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        intro k hk
        dsimp only [coneStep]
        simp (config := { congrConsts := false }) only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp (config := { congrConsts := false }) only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp (config := { congrConsts := false }); omega, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp (config := { congrConsts := false }) [List.getD_eq_getElem?_getD]
        have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          dsimp only [coneStep]
          simp (config := { congrConsts := false }) only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp (config := { congrConsts := false }) [hlen]
        rw [e2, e1]
        simp (config := { congrConsts := false }) only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp (config := { congrConsts := false }), w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - n) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          dsimp only [coneStep]
          simp (config := { congrConsts := false }) only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp (config := { congrConsts := false }); omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp (config := { congrConsts := false }) at h0
        · rintro ⟨h0, _⟩
          simp (config := { congrConsts := false }) at h0
          omega

  have inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
      InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
        (i = k ∨ InCone n C i k) := by
    have h := cones_char n C.gates i j
    delta InCone cones gateAt
    rw [h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - n, by omega, ?_, h3⟩
      have : n + (w - n) = w := by omega
      rw [this]
      exact hw
    · rintro ⟨h0, k, hk, hw, h3⟩
      refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
      have : n + k - n = k := by omega
      rw [this]
      exact h3

  have orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact le_rfl
    | head hstep _ ih =>
      obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
      omega

  have orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w') :
      ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro k h' h1 h2; left; omega
    | @head a c hstep hrest ih =>
      intro k h' h1 h2
      obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
      have hk : k0 = k := by omega
      subst hk
      have hle := orStep_le hrest
      obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
      subst hk1
      right
      rw [inCone_iff]
      exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

  have operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
      (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
      (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
    have hle := orStep_le hr
    obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
    rw [inCone_iff]
    exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩


  have orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp (config := { congrConsts := false })
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      dsimp only [orStep]
      simp (config := { congrConsts := false })
      omega

  have orSets_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp (config := { congrConsts := false })
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by
        rw [orSets_len]; simp (config := { congrConsts := false })
      have key : ∀ k, k < gs.length →
          (orStep n (gs.foldl (orStep n) []) g).getD k [] =
            (gs.foldl (orStep n) []).getD k [] := by
        intro k hk
        dsimp only [orStep]
        simp (config := { congrConsts := false }) only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp (config := { congrConsts := false }) only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp (config := { congrConsts := false }); omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp (config := { congrConsts := false }) [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
            dsimp only [orStep]
            simp (config := { congrConsts := false }) only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp (config := { congrConsts := false }) [hlen, hop]
          rw [e2]
          simp (config := { congrConsts := false }) only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp (config := { congrConsts := false }), Or.inl h3⟩
            · refine ⟨by simp (config := { congrConsts := false }), Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - n) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - n) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
            dsimp only [orStep]
            simp (config := { congrConsts := false }) only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp (config := { congrConsts := false }) [hlen, hop]
          rw [e2]
          simp (config := { congrConsts := false }) only [List.mem_singleton]
          constructor
          · intro h3
            exact ⟨by simp (config := { congrConsts := false }), Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
          dsimp only [orStep]
          simp (config := { congrConsts := false }) only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp (config := { congrConsts := false }); omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp (config := { congrConsts := false }) at h0
        · rintro ⟨h0, _⟩
          simp (config := { congrConsts := false }) at h0
          omega

  have orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
      OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
    have h := orSets_char n C.gates g k
    delta OrReaches orSets gateAt
    have e : n + k - n = k := by omega
    rw [e, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

  have reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w2) :
      ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro g h1 hg
      subst h1
      exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
    | @head a c hstep hrest ih =>
      intro g h1 hg
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

  have orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
      ∀ w, OrReaches n C w g →
        Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      have hnw : n ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
      · exact ⟨Relation.ReflTransGen.refl, hk⟩
      · obtain ⟨hr2, hg⟩ := ih i hlt hr
        exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

  have mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
      Relation.ReflTransGen (OrStep n C) p u.val := by
    dsimp only [PEqualNP.TopForm.orIn] at hu
    simp (config := { congrConsts := false }) only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rcases hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

  have reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
      u ∈ PEqualNP.TopForm.orIn n C p := by
    dsimp only [PEqualNP.TopForm.orIn]
    simp (config := { congrConsts := false }) only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

  have pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
    funext w
    dsimp only [pairInput]
    simp (config := { congrConsts := false }) only [or_comm]

  have sub_zero2 : (1 : Fin 2) - 0 = 1 := by decide

  have sub_one2 : (1 : Fin 2) - 1 = 0 := by decide

  have routes : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∀ x7 ∈ PEqualNP.TopForm.Ustar x2 x4, (∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ (x12 : Fin (2 : ℕ)), ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x9 ∈ PEqualNP.TopForm.side x4 x11 x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 ((1 : Fin (2 : ℕ)) - x12)) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ x12 ∈ PEqualNP.TopForm.junk x2 x4, ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x12 ≠ x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (0 : Fin (2 : ℕ))) x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (1 : Fin (2 : ℕ))) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true := by
    intro n G _ C hL hT e
    induction e using Sym2.ind with
    | _ u v =>
    intro huv
    obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
    dsimp only [PEqualNP.TopForm.Ustar] at huv
    simp (config := { congrConsts := false }) only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
    obtain ⟨hadj, hns⟩ := huv
    have hF : ∀ u v : Fin n, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
        (PEqualNP.EdgeOwnership.pairInput u v) = true → G.Adj u v :=
      fun u v h => (graphFun_pair G u v).mp h
    have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x :=
      fun x => congrFun hfun x
    obtain ⟨a, halen, hnor, hreach, hval⟩ :=
      edge_trace G (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
        hF hout u v ((graphFun_pair G u v).mpr hadj)
    have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op =
        PEqualNP.CircuitLowerBounds.GateOp.and := by
      rcases hAO _ (gateAt_mem halen) with h | h
      · exact h
      · exact (hnor h).elim
    have hbel : PEqualNP.TopForm.BelowF G C a := fun x hx =>
      below_of_reach
        (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) hout a hreach x hx
    have hatop : a ∈ PEqualNP.TopForm.tops G C := by
      dsimp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere]
      simp (config := { congrConsts := false }) only [Finset.mem_filter, Finset.mem_range]
      exact ⟨halen, hop, hbel⟩
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
    have e0 : PEqualNP.TopForm.opnd C a 0 = p := by
      dsimp only [PEqualNP.TopForm.opnd]
      simp (config := { congrConsts := false }) [hin]
    have e1 : PEqualNP.TopForm.opnd C a 1 = q := by
      dsimp only [PEqualNP.TopForm.opnd]
      simp (config := { congrConsts := false }) [hin]
    have hpq := (val_and (n := n) (by simp (config := { congrConsts := false })) halen hop).mp hval
    have hpin : p ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs := by rw [hin]; simp (config := { congrConsts := false })
    have hqin : q ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs := by rw [hin]; simp (config := { congrConsts := false })
    have hp := hpq p hpin
    have hq := hpq q hqin
    have junk_of : ∀ (w : ℕ), w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs →
        w < n + a → ∀ h, h < C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or →
        Relation.ReflTransGen (OrStep n C) w (n + h) →
        h ∈ PEqualNP.TopForm.junk G C ∧ ¬ PEqualNP.TopForm.BelowF G C h ∧
          PEqualNP.CleanedNonEdge.OrReaches n C w h := by
      intro w hwin hwlt h hh hhor hr
      have hhand : (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op =
          PEqualNP.CircuitLowerBounds.GateOp.and := by
        rcases hAO _ (gateAt_mem hh) with h3 | h3
        · exact h3
        · exact (hhor h3).elim
      have hcone : PEqualNP.EdgeOwnership.InCone n C h a :=
        operand_cone halen hwin hwlt hr
      have hnb : ¬ PEqualNP.TopForm.BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
      have hdirty : PEqualNP.CleanedNonEdge.IsDirtyAnd n G C h := by
        delta PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
        refine ⟨hhand, hh, ?_⟩
        by_contra hne
        apply hnb
        intro x hx
        by_contra hfx
        exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
      have hjunk : h ∈ PEqualNP.TopForm.junk G C := by
        delta PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
      exact ⟨hjunk, hnb, reach_orReaches hr h rfl hh⟩
    rcases operand_trace (C := C) u v p hp.2 with
      ⟨t1, ht1, hr1⟩ | ⟨h1, hh1, hhor1, hr1, hv1⟩
    · rcases operand_trace (C := C) u v q hq.2 with
        ⟨t2, ht2, hr2⟩ | ⟨h2', hh2, hhor2, hr2, hv2⟩
      · exfalso
        apply hns
        have hadj12 : G.Adj t1 t2 :=
          side_adj G (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
            hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
        have hne : t1 ≠ t2 := G.ne_of_adj hadj12
        have hs : s(u, v) = s(t1, t2) := by
          rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
          · exact (hne (h1.trans h2.symm)).elim
          · rw [h1, h2]
          · rw [h1, h2]; exact Sym2.eq_swap
          · exact (hne (h1.trans h2.symm)).elim
        rw [hs]
        dsimp only [PEqualNP.TopForm.starEdges]
        simp (config := { congrConsts := false }) only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
        refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
        · dsimp only [PEqualNP.TopForm.side]
          simp (config := { congrConsts := false }) only [e0]
          exact reach_mem_orIn t1 hr1
        · dsimp only [PEqualNP.TopForm.side]
          simp (config := { congrConsts := false }) only [e1]
          exact reach_mem_orIn t2 hr2
      · obtain ⟨hj, _, hor⟩ := junk_of q hqin hq.1 h2' hh2 hhor2 hr2
        left
        have hside : t1 ∈ PEqualNP.TopForm.side C a 0 := by
          dsimp only [PEqualNP.TopForm.side]
          simp (config := { congrConsts := false }) only [e0]
          exact reach_mem_orIn t1 hr1
        have hor' : PEqualNP.CleanedNonEdge.OrReaches n C
            (PEqualNP.TopForm.opnd C a ((1 : Fin 2) - 0)) h2' := by
          rw [sub_zero2, e1]; exact hor
        rcases ht1 with rfl | rfl
        · exact ⟨t1, v, rfl, a, hatop, 0, h2', hj, hside, hor', hv2⟩
        · refine ⟨t1, u, Sym2.eq_swap, a, hatop, 0, h2', hj, hside, hor', ?_⟩
          rw [pairInput_comm]; exact hv2
    · obtain ⟨hj1, hnb1, hor1⟩ := junk_of p hpin hp.1 h1 hh1 hhor1 hr1
      rcases operand_trace (C := C) u v q hq.2 with
        ⟨t2, ht2, hr2⟩ | ⟨h2', hh2, hhor2, hr2, hv2⟩
      · left
        have hside : t2 ∈ PEqualNP.TopForm.side C a 1 := by
          dsimp only [PEqualNP.TopForm.side]
          simp (config := { congrConsts := false }) only [e1]
          exact reach_mem_orIn t2 hr2
        have hor' : PEqualNP.CleanedNonEdge.OrReaches n C
            (PEqualNP.TopForm.opnd C a ((1 : Fin 2) - 1)) h1 := by
          rw [sub_one2, e0]; exact hor1
        rcases ht2 with rfl | rfl
        · exact ⟨t2, v, rfl, a, hatop, 1, h1, hj1, hside, hor', hv1⟩
        · refine ⟨t2, u, Sym2.eq_swap, a, hatop, 1, h1, hj1, hside, hor', ?_⟩
          rw [pairInput_comm]; exact hv1
      · obtain ⟨hj2, _, hor2⟩ := junk_of q hqin hq.1 h2' hh2 hhor2 hr2
        right
        refine ⟨u, v, rfl, a, hatop, h1, hj1, h2', hj2, ?_, ?_, ?_, hv1, hv2⟩
        · intro heq
          subst heq
          apply hnb1
          intro x hx
          apply hbel
          show val C (List.ofFn x) (n + a) = true
          rw [val_and (n := n) (by simp (config := { congrConsts := false })) halen hop, hin]
          intro i hi
          simp (config := { congrConsts := false }) only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨hp.1, orStep_up (n := n) (by simp (config := { congrConsts := false })) hr1 hx⟩
          · exact ⟨hq.1, orStep_up (n := n) (by simp (config := { congrConsts := false })) hr2 hx⟩
        · rw [e0]; exact hor1
        · rw [e1]; exact hor2
  obtain ⟨cLeaf, hLeaf⟩ := leafBound
  obtain ⟨cDouble, hDouble⟩ := doubleBound
  refine ⟨cLeaf + cDouble, ?_⟩
  intro n G _ hGirth hEdge C hLeast hTop
  let R := ((Ustar G C).filter (fun e => ¬ ∃ u v : Fin n, e = s(u,v) ∧
      ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n+h)).card ∧
        (∀ w ∈ orIn n C (n+h), G.Adj u w) ∧ orIn n C (opnd C h b) = {v}))
  let A : Sym2 (Fin n) → Prop := (fun e => ∃ u v : Fin n, e = s(u,v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1-b)) h ∧
        gateVal n C h (pairInput u v) = true)
  let B : Sym2 (Fin n) → Prop := (fun e => ∃ u v : Fin n, e = s(u,v) ∧
      ∃ a ∈ tops G C, ∃ h ∈ junk G C, ∃ h' ∈ junk G C,
        h ≠ h' ∧ OrReaches n C (opnd C a 0) h ∧ OrReaches n C (opnd C a 1) h' ∧
        gateVal n C h (pairInput u v) = true ∧ gateVal n C h' (pairInput u v) = true)
  have hA : (R.filter A).card ≤ cLeaf * (C.size + 1) :=
    hLeaf n G hGirth hEdge C hLeast hTop
  have hB : (R.filter B).card ≤ cDouble * (C.size + 1) :=
    hDouble n G hGirth hEdge C hLeast hTop
  have hcover : R ⊆ R.filter A ∪ R.filter B := by
    intro e he
    have hu : e ∈ Ustar G C := (Finset.mem_filter.mp he).1
    rcases routes n G C hLeast hTop e hu with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, hb⟩)
  change R.card ≤ (cLeaf + cDouble) * (C.size + 1)
  calc
    R.card ≤ (R.filter A ∪ R.filter B).card := Finset.card_le_card hcover
    _ ≤ (R.filter A).card + (R.filter B).card := Finset.card_union_le _ _
    _ ≤ cLeaf * (C.size + 1) + cDouble * (C.size + 1) := Nat.add_le_add hA hB
    _ = (cLeaf + cDouble) * (C.size + 1) := (Nat.add_mul ..).symm
