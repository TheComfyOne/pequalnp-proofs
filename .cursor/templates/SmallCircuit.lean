import Mathlib
import PEqualNP.Defs

/-
  Local template (not a desk submission). A concrete fan-in-two AND/OR circuit
  for the edge function of K2,2, checked with decide, in the same shape as the
  g2x3 / 3-cube existence steps.

  Inputs 0,1 are one part of the bipartition; inputs 2,3 the other. The edge
  function is
      (z0 && z2) || (z0 && z3) || (z1 && z2) || (z1 && z3)
  which factors as (z0 || z1) && (z2 || z3). That is the F of L_meta_2121.

  Wire numbering (CircuitLowerBounds): inputs occupy 0 .. n-1; gate j writes
  wire n+j. For n = 4:
      gate 0: OR  of wires 0,1  -> wire 4
      gate 1: OR  of wires 2,3  -> wire 5
      gate 2: AND of wires 4,5  -> wire 6
  output 6, size 3. Same construction idea as the 3-gate witness in L_meta_5599
  (there n = 8 because the representation uses oneEach on 4+4 bits).

  Build with:
      cd lean && lake env lean ../.cursor/templates/SmallCircuit.lean
-/

namespace PEqualNP.Cursor.SmallCircuit

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def F (z : Fin 4 → Bool) : Bool :=
  (z 0 && z 2) || (z 0 && z 3) || (z 1 && z 2) || (z 1 && z 3)

def C : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩

theorem mono : Monotone2 C := by
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem reads : ReadsBack 4 C := by
  intro j hj i hi
  have : j < 3 := by
    simpa [C, Circuit.size] using hj
  interval_cases j <;> (
    simp [C, NestedCover.gateAt] at hi
    omega)

theorem size_le : C.size ≤ 3 := by
  simp [C, Circuit.size]

theorem evals (a b c d : Bool) :
    C.eval [a, b, c, d] = ((a || b) && (c || d)) := by
  decide +revert

theorem ofFn4 (a b c d : Bool) :
    List.ofFn (![a, b, c, d] : Fin 4 → Bool) = [a, b, c, d] := by
  simp [List.ofFn_succ]

theorem vec4 (x : Fin 4 → Bool) : x = ![x 0, x 1, x 2, x 3] := by
  ext i; fin_cases i <;> rfl

-- decide enumerates the 16 assignments of a,b,c,d. Use +revert so those
-- free Bools become quantified (otherwise decide refuses the goal).
theorem computes (a b c d : Bool) :
    C.eval (List.ofFn (![a, b, c, d] : Fin 4 → Bool)) =
      F (![a, b, c, d]) := by
  decide +revert

theorem computes_all : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = F x := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3] := vec4 x
  rw [hx]
  exact computes (x 0) (x 1) (x 2) (x 3)

theorem exists_circuit :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 4 D ∧ D.size ≤ 3 ∧
      ∀ x : Fin 4 → Bool, D.eval (List.ofFn x) = F x :=
  ⟨C, mono, reads, size_le, computes_all⟩

end PEqualNP.Cursor.SmallCircuit
