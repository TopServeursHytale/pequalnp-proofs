import Mathlib
import PEqualNP.Defs

-- Proposed two-part cut of L-meta-2462.
-- The first hypothesis isolates reverse-mode construction of coefficients linear
-- in the line inputs. Constants are allowed as zero-input AND/OR gates.
-- The second hypothesis isolates the multi-output lower bound from geometry.
-- It applies to monotone functions dominated by neighborhood disjunctions.

theorem PEqualNP.Outside.R_meta_2462_724 :
  (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.TopForm.IsAO2 (N + N) C →
    (∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧
        z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin N → ℕ),
      (∀ g ∈ D.gates,
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      D.size ≤ 8 * C.size ∧
      (∀ (l : Fin N) (x : Fin N → Bool),
        PEqualNP.MetaComplexity.circuitFun N { D with output := o l } x = true →
        ∃ p : Fin N, I p l ∧ x p = true) ∧
      (∀ p l : Fin N, I p l →
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i))
          p.val (N + l.val) = true →
        PEqualNP.MetaComplexity.circuitFun N { D with output := o l }
          (fun p' => decide (p' = p)) = true) ∧
      Fintype.card { l : Fin N // ∃ p : Fin N,
        PEqualNP.MetaComplexity.circuitFun N { D with output := o l }
          (fun p' => decide (p' = p)) = true } ≤ 2 * C.size) →
  (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin N → ℕ),
    (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
    (∀ g ∈ D.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (l : Fin N) (x : Fin N → Bool),
      PEqualNP.MetaComplexity.circuitFun N { D with output := o l } x = true →
      ∃ p : Fin N, I p l ∧ x p = true) →
    Fintype.card { e : Fin N × Fin N //
      PEqualNP.MetaComplexity.circuitFun N { D with output := o e.2 }
        (fun p' => decide (p' = e.1)) = true } ≤
      D.size + Fintype.card { l : Fin N // ∃ p : Fin N,
        PEqualNP.MetaComplexity.circuitFun N { D with output := o l }
          (fun p' => decide (p' = p)) = true }) →
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x3 x12 x13 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x2 x13) = Bool.true)) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.true } ≤ (33 : ℕ) * x5.size := by
  intro hExtract hMulti q N I _ C hq hN hline hunique hC heval
  classical
  obtain ⟨D, o, hD, hsize, hdom, hcover, hactive⟩ := hExtract N I C hC heval
  have hcount := hMulti N I D o hunique hD hdom
  let lift :
      { e : Fin N × Fin N // I e.1 e.2 ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i))
          e.1.val (N + e.2.val) = true } →
      { e : Fin N × Fin N //
        PEqualNP.MetaComplexity.circuitFun N { D with output := o e.2 }
          (fun p' => decide (p' = e.1)) = true } :=
    fun e => ⟨e.val, hcover e.val.1 e.val.2 e.property.1 e.property.2⟩
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact h
  have hsub := Fintype.card_le_of_injective lift hinj
  omega
