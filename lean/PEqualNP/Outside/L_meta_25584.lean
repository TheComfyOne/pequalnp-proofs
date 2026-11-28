import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25534

namespace PEqualNP.Outside.L_meta_25584

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def G : Fin 5 → Fin 25 → Bool :=
  fun u c => decide (u.val = c.val / 5 ∨ u.val = c.val % 5)

def code : Fin 25 → Fin 5 → Bool :=
  fun c i => decide (i.val = c.val / 5 ∨ i.val = c.val % 5)

theorem pair_ok : ∀ u v : Fin 5, u ≠ v → ∃ c : Fin 25, G u c = true ∧ G v c = false := by
  intro u v hne
  have hu : u.val < 5 := u.isLt
  refine ⟨⟨5 * u.val + u.val, by omega⟩, ?_⟩
  have hdiv : (5 * u.val + u.val) / 5 = u.val := by omega
  have hmod : (5 * u.val + u.val) % 5 = u.val := by omega
  have hne' : v.val ≠ u.val := fun h => hne (Fin.ext h.symm)
  simp [G, hdiv, hmod, hne']

theorem triple_ok :
    ∀ u v w : Fin 5, u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin 25, G u c = true ∧ G v c = true ∧ G w c = false := by
  intro u v w huv huw hvw
  have hu : u.val < 5 := u.isLt
  have hv : v.val < 5 := v.isLt
  refine ⟨⟨5 * u.val + v.val, by omega⟩, ?_⟩
  have hdiv : (5 * u.val + v.val) / 5 = u.val := by omega
  have hmod : (5 * u.val + v.val) % 5 = v.val := by omega
  have hw1 : w.val ≠ u.val := fun h => huw (Fin.ext h.symm)
  have hw2 : w.val ≠ v.val := fun h => hvw (Fin.ext h.symm)
  simp [G, hdiv, hmod, hw1, hw2]

theorem eval_as_pair (c : Fin 25) (a b : Fin 5)
    (ha : a.val = c.val / 5) (hb : b.val = c.val % 5) :
    (∀ i : Fin 5, code c i = decide (i = a ∨ i = b)) ∧
      ∀ u : Fin 5, G u c = decide (u = a ∨ u = b) := by
  constructor
  · intro i
    have : (i = a ∨ i = b) ↔ (i.val = c.val / 5 ∨ i.val = c.val % 5) := by
      simp [Fin.ext_iff, ha, hb]
    simp [code, this]
  · intro u
    have : (u = a ∨ u = b) ↔ (u.val = c.val / 5 ∨ u.val = c.val % 5) := by
      simp [Fin.ext_iff, ha, hb]
    simp [G, this]

end PEqualNP.Outside.L_meta_25584

theorem PEqualNP.Outside.L_meta_25584 :
    (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧
      ∀ (u a b : Fin 5),
        C.eval (List.ofFn (fun i : Fin 5 => decide (i = u)) ++
          List.ofFn (fun i : Fin 5 => decide (i = a ∨ i = b))) = decide (u = a ∨ u = b))) := by
  rintro ⟨C, hMono, hSize, hEval⟩
  have hEval' : ∀ (u : Fin 5) (c : Fin 25),
      C.eval (List.ofFn (fun i : Fin 5 => decide (i = u)) ++
        List.ofFn (PEqualNP.Outside.L_meta_25584.code c)) =
        PEqualNP.Outside.L_meta_25584.G u c := by
    intro u c
    let a : Fin 5 := ⟨c.val / 5, by have := c.isLt; omega⟩
    let b : Fin 5 := ⟨c.val % 5, Nat.mod_lt _ (by decide : (0 : ℕ) < 5)⟩
    have hc := PEqualNP.Outside.L_meta_25584.eval_as_pair c a b rfl rfl
    have hx : List.ofFn (PEqualNP.Outside.L_meta_25584.code c) =
        List.ofFn (fun i : Fin 5 => decide (i = a ∨ i = b)) := by
      refine List.ofFn_inj.mpr ?_
      funext i
      exact hc.1 i
    rw [hx, hc.2 u]
    exact hEval u a b
  have hLower : 9 ≤ C.size :=
    PEqualNP.Outside.L_meta_25534 5 25 5
      PEqualNP.Outside.L_meta_25584.G
      PEqualNP.Outside.L_meta_25584.code C (by decide)
      PEqualNP.Outside.L_meta_25584.pair_ok
      PEqualNP.Outside.L_meta_25584.triple_ok hMono hEval'
  exact (by decide : ¬ (9 ≤ 8)) (hLower.trans hSize)
