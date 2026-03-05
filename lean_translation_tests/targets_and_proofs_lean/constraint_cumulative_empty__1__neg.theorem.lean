
import Mathlib
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


-- These lines work to assume that every Prop is decidable. I.e. if p : Prop, then (decide p) will always work
open Classical
noncomputable section
classical



-- MiniZinc Array Types. Represents MiniZinc arrays of dimensions 1 through 8 in Lean.
-- The array contents are modelled by toFun, dom0 through domN are the array boundaries. Boundaries for accesses are enforced through safety formulas.

universe u

/-- Helper: product of a list of Nats. -/
def listProd : List Nat → Nat := List.foldl (· * ·) 1

/-- Nonempty contiguous finite integer set. -/
def mzIsContiguousIntSet (s : Finset Int) : Prop :=
    0 < s.card ∧ Int.ofNat s.card = (s.max.getD 0 - s.min.getD 0 + 1)

/-- 1D array with element type α. -/
structure Array1d (α : Type u) where
    dom0  : Finset Int
    toFun : Int → α

/-- 2D array with element type α. -/
structure Array2d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    toFun : Int → Int → α

/-- 3D array with element type α. -/
structure Array3d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    toFun : Int → Int → Int → α

/-- 4D array with element type α. -/
structure Array4d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    toFun : Int → Int → Int → Int → α

/-- 5D array with element type α. -/
structure Array5d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    toFun : Int → Int → Int → Int → Int → α

/-- 6D array with element type α. -/
structure Array6d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    dom5  : Finset Int
    toFun : Int → Int → Int → Int → Int → Int → α

/-- 7D array with element type α. -/
structure Array7d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    dom5  : Finset Int
    dom6  : Finset Int
    toFun : Int → Int → Int → Int → Int → Int → Int → α

/-- 8D array with element type α. -/
structure Array8d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    dom5  : Finset Int
    dom6  : Finset Int
    dom7  : Finset Int
    toFun : Int → Int → Int → Int → Int → Int → Int → Int → α

namespace Array1d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array1d α) : Nat :=
    listProd [a.dom0.card]

end Array1d

namespace Array2d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array2d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card]

end Array2d

namespace Array3d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array3d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card]

end Array3d

namespace Array4d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array4d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card]

end Array4d

namespace Array5d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array5d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card]

end Array5d

namespace Array6d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array6d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card, a.dom5.card]

end Array6d

namespace Array7d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array7d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card, a.dom5.card, a.dom6.card]

end Array7d

namespace Array8d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array8d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card, a.dom5.card, a.dom6.card, a.dom7.card]

end Array8d

-- Other definitions:

def mz_bool2int (b : Prop) : Int := if b then (1 : Int) else (0 : Int)

-- The compiled MiniZinc model with the constraints to prove:

structure Model where
  var_N : Int
  var_starts : (Array1d Int)
  var_durations : (Array1d Int)
  var_reqs : (Array1d Int)
  var_c : Prop

def cons₀ (m₀ : Model) : Prop := m₀.var_N = 0
def cons₁ (m₀ : Model) : Prop := (m₀.var_starts.dom0 = (Finset.Icc 1 m₀.var_N)) ∧ (∀ _i₂ ∈ m₀.var_starts.dom0, (m₀.var_starts.toFun _i₂) ∈ (Finset.Icc 0 0))
def cons₂ (m₀ : Model) : Prop := (m₀.var_durations.dom0 = (Finset.Icc 1 m₀.var_N)) ∧ (∀ _i₅ ∈ m₀.var_durations.dom0, (m₀.var_durations.toFun _i₅) ∈ (Finset.Icc 0 0))
def cons₃ (m₀ : Model) : Prop := (m₀.var_reqs.dom0 = (Finset.Icc 1 m₀.var_N)) ∧ (∀ _i₈ ∈ m₀.var_reqs.dom0, (m₀.var_reqs.toFun _i₈) ∈ (Finset.Icc 0 0))
def cons₄ (m₀ : Model) : Prop := (let _i₁₁ := (Finset.Icc 1 m₀.var_N); ((_i₁₁.card = 0) ∨ (∀ _i₉, (∑ _i₁₀ ∈ _i₁₁, if (m₀.var_starts.toFun (_i₁₀) ) <= _i₉ /\ (m₀.var_starts.toFun (_i₁₀) ) + (m₀.var_durations.toFun (_i₁₀) ) > _i₉ then (m₀.var_reqs.toFun (_i₁₀) ) else 0) <= 0)))
def cons₅ (m₀ : Model) : Prop := m₀.var_c = (let _i₂₄ := (Finset.Icc 1 m₀.var_N); ((_i₂₄.card = 0) ∨ (∀ _i₂₂, (∑ _i₂₃ ∈ _i₂₄, if (m₀.var_starts.toFun (_i₂₃) ) <= _i₂₂ /\ (m₀.var_starts.toFun (_i₂₃) ) + (m₀.var_durations.toFun (_i₂₃) ) > _i₂₂ then (m₀.var_reqs.toFun (_i₂₃) ) else 0) <= 0)))
def cons₆ (m₀ : Model) : Prop := (¬m₀.var_c)

theorem theorem_redundant (m₀: Model) (h₀: cons₀ m₀) (h₁: cons₁ m₀) (h₂: cons₂ m₀) (h₃: cons₃ m₀) (h₄: cons₄ m₀) (h₅: cons₅ m₀) : (cons₆ m₀) := by
  sorry
