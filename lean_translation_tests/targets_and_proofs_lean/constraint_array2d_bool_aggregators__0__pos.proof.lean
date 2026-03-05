
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
  var_B : (Array2d Prop)

def cons₀ (m₀ : Model) : Prop := (m₀.var_B.dom0 = (Finset.Icc 1 2)) ∧ (m₀.var_B.dom1 = (Finset.Icc 1 2))
def cons₁ (m₀ : Model) : Prop := ((((((m₀.var_B.toFun 1 1 )) ↔ True) ∧ (((m₀.var_B.toFun 1 2 )) ↔ True)) ∧ (((m₀.var_B.toFun 2 1 )) ↔ True)) ∧ (((m₀.var_B.toFun 2 2 )) ↔ False))
def cons₂ (m₀ : Model) : Prop := ((∃ var_i ∈ (Finset.Icc 1 2), ∃ var_j ∈ (Finset.Icc 1 2), ((m₀.var_B.toFun var_i var_j ))) ∧ (¬(∀ var_i ∈ (Finset.Icc 1 2), ∀ var_j ∈ (Finset.Icc 1 2), ((m₀.var_B.toFun var_i var_j )))))
def safe_cons₂ (m₀ : Model) : Prop := (∀ var_i ∈ (Finset.Icc 1 2), ∀ var_j ∈ (Finset.Icc 1 2), (var_i ∈ ((Finset.Icc 1 2)) ∧ var_j ∈ ((Finset.Icc 1 2))) ∧ ∀ var_i ∈ (Finset.Icc 1 2), ∀ var_j ∈ (Finset.Icc 1 2), (var_i ∈ ((Finset.Icc 1 2)) ∧ var_j ∈ ((Finset.Icc 1 2))))

theorem theorem_redundant (m₀: Model) (h₀: cons₀ m₀) (h₁: cons₁ m₀) : (cons₂ m₀) ∧ (safe_cons₂ m₀) := by
  
  -- extract the useful equivalences from cons₁
  have h11 : (m₀.var_B.toFun 1 1) ↔ True := h₁.1.1.1
  have h12 : (m₀.var_B.toFun 1 2) ↔ True := h₁.1.1.2
  have h21 : (m₀.var_B.toFun 2 1) ↔ True := h₁.1.2
  have h22 : (m₀.var_B.toFun 2 2) ↔ False := h₁.2
  -- obtain concrete truth values
  have h_true_11 : m₀.var_B.toFun 1 1 := (h11.mpr trivial)
  have h_true_12 : m₀.var_B.toFun 1 2 := (h12.mpr trivial)
  have h_true_21 : m₀.var_B.toFun 2 1 := (h21.mpr trivial)
  have h_false_22 : ¬ m₀.var_B.toFun 2 2 := by
    intro h
    have : False := (h22.mp h)
    exact this.elim
  -- build the existential part of cons₂
  have h_exist : ∃ var_i ∈ Finset.Icc 1 2,
      ∃ var_j ∈ Finset.Icc 1 2, m₀.var_B.toFun var_i var_j := by
    refine ⟨1, ?_, ?_⟩
    · simp
    · refine ⟨1, ?_, ?_⟩
      · simp
      · exact h_true_11
  -- build the negated universal part
  have h_notforall :
      ¬ (∀ var_i ∈ Finset.Icc 1 2, ∀ var_j ∈ Finset.Icc 1 2, m₀.var_B.toFun var_i var_j) := by
    intro hforall
    have h22' := hforall 2 (by simp) 2 (by simp)
    exact h_false_22 h22'
  have h_cons₂ : cons₂ m₀ := by
    exact ⟨h_exist, h_notforall⟩
  -- prove the safe_cons₂ condition (trivial)
  have h_safe : safe_cons₂ m₀ := by
    intro i hi j hj
    refine ⟨?first, ?second⟩
    · exact ⟨hi, hj⟩
    · intro i2 hi2 j2 hj2
      exact ⟨hi2, hj2⟩
  exact ⟨h_cons₂, h_safe⟩
