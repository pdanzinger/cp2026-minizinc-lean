
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
  var_S : (Finset Int)
  var_A : (Array1d Int)
  var_B : (Array1d Prop)

def cons₀ (m₀ : Model) : Prop := m₀.var_S = ({2, 4, 5} : Finset Int)
def cons₁ (m₀ : Model) : Prop := (m₀.var_A.dom0 = (Finset.Icc 1 3)) ∧ m₀.var_A = (({toFun := (fun (_i₂ : Int) => match _i₂ with  | (1 : Int) => 2 | (2 : Int) => 4 | (3 : Int) => 5 | _ => 2), dom0 := (Finset.Icc 1 3)} : (Array1d Int)))
def cons₂ (m₀ : Model) : Prop := (m₀.var_B.dom0 = (Finset.Icc 1 2))
def cons₃ (m₀ : Model) : Prop := ((((m₀.var_B.toFun 1 )) ↔ True) ∧ (((m₀.var_B.toFun 2 )) ↔ False))
def cons₄ (m₀ : Model) : Prop := (((let _i₆ : WithTop Int := (Finset.Icc 1 3).inf (fun _i₅ => ((m₀.var_A.toFun (_i₅) ) : WithTop Int)); _i₆.getD 0) = 2) ∧ ((let _i₄ : WithBot Int := (Finset.Icc 1 3).sup (fun _i₃ => ((m₀.var_A.toFun (_i₃) ) : WithBot Int)); _i₄.getD 0) = 5))
def safe_cons₄ (m₀ : Model) : Prop := ((0 < ((Finset.Icc 1 3)).card) ∧ (0 < ((Finset.Icc 1 3)).card))

theorem theorem_redundant (m₀: Model) (h₀: cons₀ m₀) (h₁: cons₁ m₀) (h₂: cons₂ m₀) (h₃: cons₃ m₀) : (cons₄ m₀) ∧ (safe_cons₄ m₀) := by
  
  /- Diagnosis:
     The error persists because `simp` in the proofs of `h_inf` and `h_sup` still leaves coercion goals.
     The issue is that `Finset.inf_insert` and `Finset.inf_singleton` don't fully simplify the coercions.
     Instead, we can use a direct computation approach: compute the inf and sup by evaluating the function
     at all points in the set. Since the set is small ({1,2,3}), we can explicitly compute the values.
     We'll use `Finset.inf_of_mem` and `Finset.sup_of_mem` lemmas, or simply use `decide` on the entire
     equality after rewriting the set to {1,2,3} and substituting the known function values.
  -/
  have hA1 : m₀.var_A.toFun 1 = 2 := by simp [h₁.right]
  have hA2 : m₀.var_A.toFun 2 = 4 := by simp [h₁.right]
  have hA3 : m₀.var_A.toFun 3 = 5 := by simp [h₁.right]
  have h_set : Finset.Icc (1 : Int) 3 = ({1, 2, 3} : Finset Int) := by decide
  have h_inf : (Finset.Icc 1 3).inf (fun i => (m₀.var_A.toFun i : WithTop Int)) = (2 : WithTop Int) := by
    rw [h_set]
    -- Now the set is {1,2,3}. Compute the inf by cases.
    simp [Finset.inf_insert, Finset.inf_singleton, hA1, hA2, hA3]
    -- The remaining goal is (2 : WithTop Int) = (2 : WithTop Int) ⊓ (4 : WithTop Int) ⊓ (5 : WithTop Int)
    -- This is true because 2 is the minimum. We can prove it by `decide` since all values are concrete.
    decide
  have h_sup : (Finset.Icc 1 3).sup (fun i => (m₀.var_A.toFun i : WithBot Int)) = (5 : WithBot Int) := by
    rw [h_set]
    simp [Finset.sup_insert, Finset.sup_singleton, hA1, hA2, hA3]
    decide
  have h_cons4 : cons₄ m₀ := by
    unfold cons₄
    constructor
    · rw [h_inf]
      rfl
    · rw [h_sup]
      rfl
  have h_safe : safe_cons₄ m₀ := by
    unfold safe_cons₄
    constructor <;> decide
  exact ⟨h_cons4, h_safe⟩
