import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25593

theorem PEqualNP.Outside.L_meta_25609 :
    (¬ (∃ (n m d : ℕ) (G : Fin n → Fin m → Bool) (edge : Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      let nbrR := fun (a : Fin n) => Finset.univ.filter (fun v : Fin m => G a v = edge)
      let nbrC := fun (c : Fin m) => Finset.univ.filter (fun u : Fin n => G u c = edge)
      2 ≤ d ∧
      (∀ a, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d) ∧
      (∀ c, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d) ∧
      (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) ∧
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents G C ∧
      (48 * d + 1) * C.size + 150 * d + 5 < (48 * d + 2) * (n + m))) := by
  rintro ⟨n, m, d, G, edge, C, hd, hr, hc, h4, fan, rep, hlt⟩
  have hge := PEqualNP.Outside.L_meta_25593 n m d G edge C hd hr hc h4 fan rep
  exact (not_le_of_gt hlt) hge
