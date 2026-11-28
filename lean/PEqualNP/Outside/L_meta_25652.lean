import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25645

theorem PEqualNP.Outside.L_meta_25652 :
    (¬ (∃ (n m d : ℕ) (G : Fin n → Fin m → Bool) (edge : Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      let nbrR := fun (a : Fin n) => Finset.univ.filter (fun v : Fin m => G a v = edge)
      let nbrC := fun (c : Fin m) => Finset.univ.filter (fun u : Fin n => G u c = edge)
      2 ≤ d ∧
      (∀ a, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d) ∧
      (∀ c, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d) ∧
      (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) ∧
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents G C ∧
      let negs := C.gates.countP (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))
      28 * d * C.size + 78 * d + 2 < (28 * d + 1) * (n + m) + 12 * d * negs)) := by
  rintro ⟨n, m, d, G, edge, C, hd, hr, hc, h4, fan, rep, hlt⟩
  have hge := PEqualNP.Outside.L_meta_25645 n m d G edge C hd hr hc h4 fan rep
  exact (not_le_of_gt hlt) hge
