import Mathlib.Data.Finset.Card

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4630_171
    (positive : ∀ (a b : Fin 11 → ℕ × Bool) (v : ℕ → (Fin 8 → Bool) → Bool) (o : Fin 20),
      (∀ j : Fin 11, (a j).1 < 9 + j.val ∧ (b j).1 < 9 + j.val) →
      (∀ (i : Fin 8) (x : Fin 8 → Bool), v i.val x = x i) →
      (∀ x, v 8 x = false) →
      (∀ (j : Fin 11) x, v (9 + j.val) x = ((v (a j).1 x ^^ (a j).2) && (v (b j).1 x ^^ (b j).2))) →
      ∃ x, (v o.val x ^^ false) ≠ ([1, 12, 23, 4, 15, 26, 37, 46, 57, 47] : List ℕ).any
        (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))))
    (negative : ∀ (a b : Fin 11 → ℕ × Bool) (v : ℕ → (Fin 8 → Bool) → Bool) (o : Fin 20),
      (∀ j : Fin 11, (a j).1 < 9 + j.val ∧ (b j).1 < 9 + j.val) →
      (∀ (i : Fin 8) (x : Fin 8 → Bool), v i.val x = x i) →
      (∀ x, v 8 x = false) →
      (∀ (j : Fin 11) x, v (9 + j.val) x = ((v (a j).1 x ^^ (a j).2) && (v (b j).1 x ^^ (b j).2))) →
      ∃ x, (v o.val x ^^ true) ≠ ([1, 12, 23, 4, 15, 26, 37, 46, 57, 47] : List ℕ).any
        (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))))
    : ∀ (x1 : ℕ → (Fin (8 : ℕ) → Bool) → Bool) (x2 : Finset ℕ), x2.card ≤ (11 : ℕ) →
      (∀ x4 < (23 : ℕ),
        (∃ (x6 : Bool), ∀ (x7 : Fin (8 : ℕ) → Bool), x1 x4 x7 = x6) ∨
        (∃ (x6 : Fin (8 : ℕ)) (x7 : Bool), ∀ (x8 : Fin (8 : ℕ) → Bool), x1 x4 x8 = (x8 x6 ^^ x7)) ∨
        (∃ x6 < x4, ∃ (x7 : Bool), ∀ (x8 : Fin (8 : ℕ) → Bool), x1 x4 x8 = (x1 x6 x8 ^^ x7)) ∨
        x4 ∈ x2 ∧ ∃ x6 < x4, ∃ x7 < x4, ∃ (x8 : Bool) (x9 : Bool) (x10 : Bool),
          ∀ (x11 : Fin (8 : ℕ) → Bool), x1 x4 x11 =
            if x10 = Bool.true then (x1 x6 x11 ^^ x8) && (x1 x7 x11 ^^ x9)
            else x1 x6 x11 ^^ x8 || x1 x7 x11 ^^ x9) →
      ∀ x5 < (23 : ℕ), ∃ (x7 : Fin (8 : ℕ) → Bool),
        x1 x5 x7 ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (4 : ℕ), (15 : ℕ),
          (26 : ℕ), (37 : ℕ), (46 : ℕ), (57 : ℕ), (47 : ℕ)].any fun (x8 : ℕ) =>
            x7 (Fin.ofNat (8 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (8 : ℕ) (x8 % (10 : ℕ))) := by
  classical
  intro w paid hBudget hWire o ho
  let Valid (k : ℕ) (a b : ℕ → ℕ × Bool) (v : ℕ → (Fin 8 → Bool) → Bool) :=
    (∀ j < k, (a j).1 < 9 + j ∧ (b j).1 < 9 + j) ∧
    (∀ (i : Fin 8) x, v i.val x = x i) ∧ (∀ x, v 8 x = false) ∧
    (∀ j < k, ∀ x, v (9 + j) x = ((v (a j).1 x ^^ (a j).2) && (v (b j).1 x ^^ (b j).2)))
  have translate : ∀ u v s t p q d : Bool,
      (if d = true then ((u ^^ s) ^^ p) && ((v ^^ t) ^^ q)
       else ((u ^^ s) ^^ p) || ((v ^^ t) ^^ q)) =
        (((u ^^ ((s ^^ p) ^^ !d)) && (v ^^ ((t ^^ q) ^^ !d))) ^^ !d) := by decide
  -- Each of the first n wires is represented by a wire and a polarity.
  -- Only the binary case uses a new AND gate.
  have build (n : ℕ) (hn : n ≤ 23) :
      ∃ k ≤ (paid.filter (fun j => j < n)).card,
        ∃ (a b : ℕ → ℕ × Bool) (v : ℕ → (Fin 8 → Bool) → Bool),
          Valid k a b v ∧
          ∀ i < n, ∃ j < 9 + k, ∃ s : Bool, ∀ x, w i x = (v j x ^^ s) := by
    induction n with
    | zero =>
      let v (i : ℕ) (x : Fin 8 → Bool) : Bool := if h : i < 8 then x ⟨i, h⟩ else false
      refine ⟨0, Nat.zero_le _, fun _ => (8, false), fun _ => (8, false), v, ?_, by simp⟩
      refine ⟨by simp, ?_, by simp [v], by simp⟩
      intro i x
      simp [v, i.isLt]
    | succ n ih =>
      obtain ⟨k, hk, a, b, v, hValid, hRep⟩ := ih (by omega)
      have hMonotone : (paid.filter (fun j => j < n)).card ≤ (paid.filter (fun j => j < n + 1)).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, by omega⟩
      have keep (hNew : ∃ j < 9 + k, ∃ s : Bool, ∀ x, w n x = (v j x ^^ s)) :
          ∃ l ≤ (paid.filter (fun j => j < n + 1)).card,
            ∃ (a b : ℕ → ℕ × Bool) (v : ℕ → (Fin 8 → Bool) → Bool),
              Valid l a b v ∧
              ∀ i < n + 1, ∃ j < 9 + l, ∃ s : Bool, ∀ x, w i x = (v j x ^^ s) := by
        refine ⟨k, hk.trans hMonotone, a, b, v, hValid, ?_⟩
        intro i hi
        by_cases e : i = n
        · subst i
          exact hNew
        · exact hRep i (by omega)
      obtain ⟨c, hc⟩ | ⟨i, p, hp⟩ | ⟨i, hi, p, hp⟩ | ⟨hPaid, i, hi, j, hj, p, q, d, hGate⟩ :=
        hWire n (by omega)
      · apply keep
        exact ⟨8, by omega, c, fun x => by simp [hValid.2.2.1 x, hc x]⟩
      · apply keep
        exact ⟨i.val, by have := i.isLt; omega, p, fun x => by rw [hValid.2.1 i x, hp x]⟩
      · apply keep
        obtain ⟨j, hj, s, hs⟩ := hRep i hi
        exact ⟨j, hj, s ^^ p, fun x => by rw [hp x, hs x, Bool.xor_assoc]⟩
      · obtain ⟨l, hl, s, hL⟩ := hRep i hi
        obtain ⟨r, hr, t, hR⟩ := hRep j hj
        let a' (i : ℕ) : ℕ × Bool := if i = k then (l, (s ^^ p) ^^ !d) else a i
        let b' (i : ℕ) : ℕ × Bool := if i = k then (r, (t ^^ q) ^^ !d) else b i
        let v' (i : ℕ) (x : Fin 8 → Bool) := if i = 9 + k then
          (v l x ^^ ((s ^^ p) ^^ !d)) && (v r x ^^ ((t ^^ q) ^^ !d)) else v i x
        have previous (i : ℕ) (h : i < 9 + k) (x : Fin 8 → Bool) : v' i x = v i x :=
          ite_eq_right (Nat.ne_of_lt h)
        have hInsert : paid.filter (fun j => j < n + 1) = insert n (paid.filter (fun j => j < n)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_insert]
          by_cases e : i = n
          · subst i
            simp [hPaid]
          · have h : i < n + 1 ↔ i < n := by omega
            simp [e, h]
        have hCount : k + 1 ≤ (paid.filter (fun j => j < n + 1)).card := by
          rw [hInsert, Finset.card_insert_of_notMem (by simp)]
          omega
        refine ⟨k + 1, hCount, a', b', v', ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_⟩
          · intro i hi
            by_cases e : i = k
            · subst i
              simpa [a', b'] using And.intro hl hr
            · simpa [a', b', e] using hValid.1 i (by omega)
          · intro i x
            exact (previous i.val (by have := i.isLt; omega) x).trans (hValid.2.1 i x)
          · intro x
            exact (previous 8 (by omega) x).trans (hValid.2.2.1 x)
          · intro i hi x
            by_cases e : i = k
            · subst i
              simp [a', b', v', Nat.ne_of_lt hl, Nat.ne_of_lt hr]
            · have lt : i < k := by omega
              have hA := (hValid.1 i lt).1
              have hB := (hValid.1 i lt).2
              simp only [a', b', e, ite_false]
              rw [previous (9 + i) (by omega), previous (a i).1 (by omega), previous (b i).1 (by omega)]
              exact hValid.2.2.2 i lt x
        · intro i hi
          by_cases e : i = n
          · subst i
            refine ⟨9 + k, by omega, !d, fun x => ?_⟩
            rw [hGate x, hL x, hR x]
            simpa [v'] using translate (v l x) (v r x) s t p q d
          · obtain ⟨j, hj, p, hp⟩ := hRep i (by omega)
            exact ⟨j, by omega, p, fun x => by rw [previous j hj x, hp x]⟩
  obtain ⟨k, hk, a, b, v, hValid, hRep⟩ := build 23 (by omega)
  have hCount : k ≤ 11 := hk.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans hBudget)
  -- Pad to eleven gates by reading the false wire twice at every unused gate.
  let a' (j : Fin 11) : ℕ × Bool := if j.val < k then a j.val else (8, false)
  let b' (j : Fin 11) : ℕ × Bool := if j.val < k then b j.val else (8, false)
  let v' (i : ℕ) (x : Fin 8 → Bool) := if i < 9 + k then v i x else false
  have retained (i : ℕ) (h : i < 9 + k) (x : Fin 8 → Bool) : v' i x = v i x := ite_eq_left h
  have hBack (j : Fin 11) : (a' j).1 < 9 + j.val ∧ (b' j).1 < 9 + j.val := by
    by_cases hj : j.val < k
    · simpa [a', b', hj] using hValid.1 j.val hj
    · simp [a', b', hj]
      omega
  have hInputs (i : Fin 8) (x : Fin 8 → Bool) : v' i.val x = x i :=
    (retained _ (by have := i.isLt; omega) x).trans (hValid.2.1 i x)
  have hZero (x : Fin 8 → Bool) : v' 8 x = false :=
    (retained _ (by omega) x).trans (hValid.2.2.1 x)
  have hStep (j : Fin 11) (x : Fin 8 → Bool) :
      v' (9 + j.val) x = ((v' (a' j).1 x ^^ (a' j).2) && (v' (b' j).1 x ^^ (b' j).2)) := by
    by_cases hj : j.val < k
    · have hA := (hValid.1 j.val hj).1
      have hB := (hValid.1 j.val hj).2
      simp only [a', b', hj, ite_true]
      rw [retained (9 + j.val) (by omega), retained (a j.val).1 (by omega), retained (b j.val).1 (by omega)]
      exact hValid.2.2.2 j.val hj x
    · have hOutside : ¬ 9 + j.val < 9 + k := by omega
      change (if 9 + j.val < 9 + k then v (9 + j.val) x else false) = _
      simp [a', b', hj, hOutside, hZero]
  obtain ⟨j, hj, s, hs⟩ := hRep o ho
  let output : Fin 20 := ⟨j, by omega⟩
  have hOutput (x : Fin 8 → Bool) : w o x = (v' output.val x ^^ s) := by
    exact (hs x).trans (congrArg (fun b => b ^^ s) (retained j hj x).symm)
  cases s with
  | false => simpa only [hOutput] using positive a' b' v' output hBack hInputs hZero hStep
  | true => simpa only [hOutput] using negative a' b' v' output hBack hInputs hZero hStep
