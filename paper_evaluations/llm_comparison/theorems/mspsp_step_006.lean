
import Mathlib
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


-- These lines work to assume that every Prop is decidable. I.e. if p : Prop, then (decide p) will always work
open Classical
noncomputable section
classical



-- MiniZinc Array Types. Represents MiniZinc arrays of dimensions 1 through 4 in Lean.
-- The array contents are modelled by toFun, dom0 through domN are the array boundaries. Boundaries for accesses are enforced through safety formulas.

universe u

/-- Helper: product of a list of Nats. -/
def listProd : List Nat → Nat := List.foldl (· * ·) 1

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



-- The compiled MiniZinc model with the constraints to prove:


namespace Mzn

def bool2int (b : Prop) : Int := if b then (1 : Int) else (0 : Int)

def int2float (i : Int) : Float := Float.ofInt i

private def floatIntCast (y : Float) : Int :=
  if y < 0.0 then
    -Int.ofNat ((-y).toUInt64.toNat)
  else
    Int.ofNat (y.toUInt64.toNat)

def floatCeilToInt (x : Float) : Int := floatIntCast (Float.ceil x)
def floatFloorToInt (x : Float) : Int := floatIntCast (Float.floor x)
def floatRoundToInt (x : Float) : Int := floatIntCast (Float.round x)

private def foldFinsetInt {β : Type} (s : Finset Int) (init : β) (f : β → Int → β) : β :=
  (s.sort (· ≤ ·)).foldl f init

private def optMinFloat : Option Float → Option Float → Option Float
  | none, x => x
  | x, none => x
  | some a, some b => some (min a b)

private def optMaxFloat : Option Float → Option Float → Option Float
  | none, x => x
  | x, none => x
  | some a, some b => some (max a b)

def finsetMinOptFloat (s : Finset Int) (f : Int → Option Float) : Option Float :=
  foldFinsetInt s none (fun acc i => optMinFloat acc (f i))

def finsetMaxOptFloat (s : Finset Int) (f : Int → Option Float) : Option Float :=
  foldFinsetInt s none (fun acc i => optMaxFloat acc (f i))

def finsetSumFloat (s : Finset Int) (f : Int → Float) : Float :=
  foldFinsetInt s 0.0 (fun acc i => acc + f i)

end Mzn

structure Model where
  var_nActs : Int
  var_nResources : Int
  var_nSkills : Int
  var_nUnrels : Int
  var_ACT : (Finset Int)
  var_SKILL : (Finset Int)
  var_dur : (Array1d Int)
  var_sreq : (Array2d Int)
  var_full_output : Int
  var_nPrecs : Int
  var_mint : Int
  var_maxt : Int
  var_RESOURCE : (Finset Int)
  var_PREC : (Finset Int)
  var_UNREL : (Finset Int)
  var_TIME : (Finset Int)
  var_USEFUL_RES : (Array1d (Finset Int))
  var_POTENTIAL_ACT : (Array1d (Finset Int))
  var_mastery : (Array2d Prop)
  var_pred : (Array1d Int)
  var_succ : (Array1d Int)
  var_unpred : (Array1d Int)
  var_unsucc : (Array1d Int)
  var_scap : (Array1d Int)
  var_start : (Array1d Int)
  var_assign : (Array2d Prop)
  var_contrib : (Array3d Prop)
  var_overlap : (Array1d Prop)
  var_makespan : Int
  var_res_load : (Array1d Int)

def cons₀ (m₀ : Model) : Prop := ((((m₀.var_nActs >= 0) ∧ (m₀.var_nResources >= 0)) ∧ (m₀.var_nSkills >= 0)) ∧ (m₀.var_nUnrels >= 0))
def cons₁ (m₀ : Model) : Prop := m₀.var_ACT = (Finset.Icc 1 m₀.var_nActs)
def cons₂ (m₀ : Model) : Prop := m₀.var_SKILL = (Finset.Icc 1 m₀.var_nSkills)
def cons₃ (m₀ : Model) : Prop := (m₀.var_dur.dom0 = m₀.var_ACT)
def cons₄ (m₀ : Model) : Prop := (m₀.var_sreq.dom0 = m₀.var_ACT) ∧ (m₀.var_sreq.dom1 = m₀.var_SKILL)
def cons₅ (m₀ : Model) : Prop := (∀ var_a ∈ m₀.var_ACT, ∀ var_s ∈ m₀.var_SKILL, ((((m₀.var_dur.toFun var_a )) >= 0) ∧ (((m₀.var_sreq.toFun var_a var_s )) >= 0)))
def cons₆ (m₀ : Model) : Prop := (m₀.var_full_output ∈ (Finset.Icc 0 1)) ∧ m₀.var_full_output = 0
def cons₇ (m₀ : Model) : Prop := m₀.var_maxt = (∑ var_i ∈ m₀.var_ACT, ((m₀.var_dur.toFun var_i )))
def cons₈ (m₀ : Model) : Prop := m₀.var_RESOURCE = (Finset.Icc 1 m₀.var_nResources)
def cons₉ (m₀ : Model) : Prop := m₀.var_PREC = (Finset.Icc 1 m₀.var_nPrecs)
def cons₁₀ (m₀ : Model) : Prop := m₀.var_UNREL = (Finset.Icc 1 m₀.var_nUnrels)
def cons₁₁ (m₀ : Model) : Prop := m₀.var_TIME = (Finset.Icc 0 m₀.var_maxt)
def cons₁₂ (m₀ : Model) : Prop := (m₀.var_USEFUL_RES.dom0 = m₀.var_ACT) ∧ (∀ _i₂, (m₀.var_USEFUL_RES.toFun _i₂) ⊆ m₀.var_RESOURCE)
def cons₁₃ (m₀ : Model) : Prop := (m₀.var_POTENTIAL_ACT.dom0 = m₀.var_RESOURCE) ∧ (∀ _i₅, (m₀.var_POTENTIAL_ACT.toFun _i₅) ⊆ m₀.var_ACT)
def cons₁₄ (m₀ : Model) : Prop := (m₀.var_mastery.dom0 = m₀.var_RESOURCE) ∧ (m₀.var_mastery.dom1 = m₀.var_SKILL)
def cons₁₅ (m₀ : Model) : Prop := (m₀.var_pred.dom0 = m₀.var_PREC) ∧ (∀ _i₈, (m₀.var_pred.toFun _i₈) ∈ m₀.var_ACT)
def cons₁₆ (m₀ : Model) : Prop := (m₀.var_succ.dom0 = m₀.var_PREC) ∧ (∀ _i₁₁, (m₀.var_succ.toFun _i₁₁) ∈ m₀.var_ACT)
def cons₁₇ (m₀ : Model) : Prop := (m₀.var_unpred.dom0 = m₀.var_UNREL) ∧ (∀ _i₁₄, (m₀.var_unpred.toFun _i₁₄) ∈ m₀.var_ACT)
def cons₁₈ (m₀ : Model) : Prop := (m₀.var_unsucc.dom0 = m₀.var_UNREL) ∧ (∀ _i₁₇, (m₀.var_unsucc.toFun _i₁₇) ∈ m₀.var_ACT)
def cons₁₉ (m₀ : Model) : Prop := (m₀.var_scap.dom0 = m₀.var_SKILL) ∧ (∀ _i₂₀, (m₀.var_scap.toFun _i₂₀) ∈ (Finset.Icc 0 m₀.var_nResources)) ∧ m₀.var_scap = (({toFun := (fun var_s => (∑ var_r ∈ m₀.var_RESOURCE, (Mzn.bool2int ((m₀.var_mastery.toFun var_r var_s ))))), dom0 := m₀.var_SKILL} : (Array1d Int)))
def cons₂₀ (m₀ : Model) : Prop := (m₀.var_start.dom0 = m₀.var_ACT) ∧ (∀ _i₂₃, (m₀.var_start.toFun _i₂₃) ∈ m₀.var_TIME)
def cons₂₁ (m₀ : Model) : Prop := (m₀.var_assign.dom0 = m₀.var_ACT) ∧ (m₀.var_assign.dom1 = m₀.var_RESOURCE)
def cons₂₂ (m₀ : Model) : Prop := (m₀.var_contrib.dom0 = m₀.var_ACT) ∧ (m₀.var_contrib.dom1 = m₀.var_RESOURCE) ∧ (m₀.var_contrib.dom2 = m₀.var_SKILL)
def cons₂₃ (m₀ : Model) : Prop := (m₀.var_overlap.dom0 = m₀.var_UNREL)
def cons₂₄ (m₀ : Model) : Prop := (m₀.var_makespan ∈ m₀.var_TIME) ∧ m₀.var_makespan = ((m₀.var_start.toFun m₀.var_nActs ))
def cons₂₅ (m₀ : Model) : Prop := (∀ var_p ∈ m₀.var_PREC, ((((m₀.var_start.toFun ((m₀.var_pred.toFun var_p )) )) + ((m₀.var_dur.toFun ((m₀.var_pred.toFun var_p )) ))) <= ((m₀.var_start.toFun ((m₀.var_succ.toFun var_p )) ))))
def cons₂₆ (m₀ : Model) : Prop := (∀ var_u ∈ m₀.var_UNREL, (let var_i : Int := ((m₀.var_unpred.toFun var_u )); let var_j : Int := ((m₀.var_unsucc.toFun var_u )); (if (∃ var_s ∈ m₀.var_SKILL, ((((m₀.var_sreq.toFun var_i var_s )) + ((m₀.var_sreq.toFun var_j var_s ))) > ((m₀.var_scap.toFun var_s )))) then ((((m₀.var_overlap.toFun var_u )) -> ((((m₀.var_start.toFun var_i )) + ((m₀.var_dur.toFun var_i ))) <= ((m₀.var_start.toFun var_j )))) ∧ ((¬((m₀.var_overlap.toFun var_u ))) -> ((((m₀.var_start.toFun var_j )) + ((m₀.var_dur.toFun var_j ))) <= ((m₀.var_start.toFun var_i ))))) else (((¬((m₀.var_overlap.toFun var_u ))) <-> (((((m₀.var_start.toFun var_i )) + ((m₀.var_dur.toFun var_i ))) <= ((m₀.var_start.toFun var_j ))) ∨ ((((m₀.var_start.toFun var_j )) + ((m₀.var_dur.toFun var_j ))) <= ((m₀.var_start.toFun var_i ))))) ∧ (∀ var_r ∈ (((m₀.var_USEFUL_RES.toFun var_i )) ∩ ((m₀.var_USEFUL_RES.toFun var_j ))), ((((m₀.var_assign.toFun var_i var_r )) ∧ ((m₀.var_assign.toFun var_j var_r ))) -> (¬((m₀.var_overlap.toFun var_u )))))))))
def cons₂₇ (m₀ : Model) : Prop := (∀ var_a ∈ m₀.var_ACT, ∀ var_s ∈ m₀.var_SKILL, (((m₀.var_sreq.toFun var_a var_s )) > 0) -> ((∑ var_r ∈ ((m₀.var_USEFUL_RES.toFun var_a )), (Mzn.bool2int ((m₀.var_contrib.toFun var_a var_r var_s )))) = ((m₀.var_sreq.toFun var_a var_s ))))
def cons₂₈ (m₀ : Model) : Prop := (∀ var_a ∈ m₀.var_ACT, ∀ var_r ∈ ((m₀.var_USEFUL_RES.toFun var_a )), ((∑ var_s ∈ m₀.var_SKILL, if ((((m₀.var_mastery.toFun var_r var_s )) ↔ True) ∧ (((m₀.var_sreq.toFun var_a var_s )) > 0)) then (Mzn.bool2int ((m₀.var_contrib.toFun var_a var_r var_s ))) else 0) <= 1))
def cons₂₉ (m₀ : Model) : Prop := (∀ var_a ∈ m₀.var_ACT, ∀ var_r ∈ ((m₀.var_USEFUL_RES.toFun var_a )), ∀ var_s ∈ m₀.var_SKILL, ((Mzn.bool2int ((m₀.var_contrib.toFun var_a var_r var_s ))) <= (Mzn.bool2int ((m₀.var_mastery.toFun var_r var_s )))))
def cons₃₀ (m₀ : Model) : Prop := (∀ var_a ∈ m₀.var_ACT, ∀ var_r ∈ ((m₀.var_USEFUL_RES.toFun var_a )), ∀ var_s ∈ m₀.var_SKILL, (((m₀.var_sreq.toFun var_a var_s )) > 0) -> ((Mzn.bool2int ((m₀.var_contrib.toFun var_a var_r var_s ))) <= (Mzn.bool2int ((m₀.var_assign.toFun var_a var_r )))))
def cons₃₁ (m₀ : Model) : Prop := (∀ var_s ∈ m₀.var_SKILL, (∀ _i₂₄, (∑ _i₂₅ ∈ m₀.var_ACT, if (m₀.var_start.toFun _i₂₅ ) <= _i₂₄ /\ (m₀.var_start.toFun _i₂₅ ) + (m₀.var_dur.toFun _i₂₅ ) > _i₂₄ then (let var_a := _i₂₅; ((m₀.var_sreq.toFun var_a var_s ))) else 0) <= ((m₀.var_scap.toFun var_s ))))
def cons₃₂ (m₀ : Model) : Prop := (∀ _i₂₆, (∑ _i₂₇ ∈ m₀.var_ACT, if (m₀.var_start.toFun _i₂₇ ) <= _i₂₆ /\ (m₀.var_start.toFun _i₂₇ ) + (m₀.var_dur.toFun _i₂₇ ) > _i₂₆ then (let var_a := _i₂₇; (∑ var_s ∈ m₀.var_SKILL, ((m₀.var_sreq.toFun var_a var_s )))) else 0) <= m₀.var_nResources)
def cons₃₃ (m₀ : Model) : Prop := (∀ var_a ∈ m₀.var_ACT, ∀ var_r ∈ (m₀.var_RESOURCE \ ((m₀.var_USEFUL_RES.toFun var_a ))), (((m₀.var_assign.toFun var_a var_r )) ↔ False))
def cons₃₄ (m₀ : Model) : Prop := (∀ var_a ∈ m₀.var_ACT, ((∀ var_r ∈ (m₀.var_RESOURCE \ ((m₀.var_USEFUL_RES.toFun var_a ))), ∀ var_s ∈ m₀.var_SKILL, ((Mzn.bool2int ((m₀.var_contrib.toFun var_a var_r var_s ))) = 0)) ∧ (∀ var_r ∈ m₀.var_RESOURCE, ∀ var_s ∈ m₀.var_SKILL, (((m₀.var_sreq.toFun var_a var_s )) = 0) -> ((Mzn.bool2int ((m₀.var_contrib.toFun var_a var_r var_s ))) = 0))))
def cons₃₅ (m₀ : Model) : Prop := (∀ var_r ∈ m₀.var_RESOURCE, ∀ var_s ∈ m₀.var_SKILL, (((m₀.var_mastery.toFun var_r var_s )) ↔ False) -> (∀ var_a ∈ m₀.var_ACT, ((Mzn.bool2int ((m₀.var_contrib.toFun var_a var_r var_s ))) = 0)))
def cons₃₆ (m₀ : Model) : Prop := (m₀.var_res_load.dom0 = m₀.var_RESOURCE) ∧ (∀ _i₃₀, (m₀.var_res_load.toFun _i₃₀) ∈ m₀.var_TIME) ∧ m₀.var_res_load = (({toFun := (fun var_r => (∑ var_a ∈ m₀.var_ACT, (((m₀.var_dur.toFun var_a )) * (Mzn.bool2int ((m₀.var_assign.toFun var_a var_r )))))), dom0 := m₀.var_RESOURCE} : (Array1d Int)))
def cons₃₇ (m₀ : Model) : Prop := (∀ var_a ∈ m₀.var_ACT, ((∑ var_r ∈ m₀.var_RESOURCE, (Mzn.bool2int ((m₀.var_assign.toFun var_a var_r )))) >= (∑ var_s ∈ m₀.var_SKILL, ((m₀.var_sreq.toFun var_a var_s )))))
def cons₃₈ (m₀ : Model) : Prop := (∀ var_a ∈ m₀.var_ACT, ∀ var_s ∈ m₀.var_SKILL, (((m₀.var_sreq.toFun var_a var_s )) > 0) -> ((∑ var_r ∈ ((m₀.var_USEFUL_RES.toFun var_a )), if (((m₀.var_mastery.toFun var_r var_s )) ↔ True) then (Mzn.bool2int ((m₀.var_assign.toFun var_a var_r ))) else 0) >= ((m₀.var_sreq.toFun var_a var_s ))))
def safe_cons₃₈ (m₀ : Model) : Prop := ∀ var_a ∈ m₀.var_ACT, ∀ var_s ∈ m₀.var_SKILL, (((var_a ∈ (m₀.var_ACT) ∧ ∀ var_r ∈ ((m₀.var_USEFUL_RES.toFun var_a )), ((var_a ∈ (m₀.var_ACT) ∧ var_r ∈ (m₀.var_RESOURCE)) ∧ (var_r ∈ (m₀.var_RESOURCE) ∧ var_s ∈ (m₀.var_SKILL)))) ∧ (var_a ∈ (m₀.var_ACT) ∧ var_s ∈ (m₀.var_SKILL))) ∧ (var_a ∈ (m₀.var_ACT) ∧ var_s ∈ (m₀.var_SKILL)))

theorem theorem_redundant (m₀: Model) (h₀: cons₀ m₀) (h₁: cons₁ m₀) (h₂: cons₂ m₀) (h₃: cons₃ m₀) (h₄: cons₄ m₀) (h₅: cons₅ m₀) (h₆: cons₆ m₀) (h₇: cons₇ m₀) (h₈: cons₈ m₀) (h₉: cons₉ m₀) (h₁₀: cons₁₀ m₀) (h₁₁: cons₁₁ m₀) (h₁₂: cons₁₂ m₀) (h₁₃: cons₁₃ m₀) (h₁₄: cons₁₄ m₀) (h₁₅: cons₁₅ m₀) (h₁₆: cons₁₆ m₀) (h₁₇: cons₁₇ m₀) (h₁₈: cons₁₈ m₀) (h₁₉: cons₁₉ m₀) (h₂₀: cons₂₀ m₀) (h₂₁: cons₂₁ m₀) (h₂₂: cons₂₂ m₀) (h₂₃: cons₂₃ m₀) (h₂₄: cons₂₄ m₀) (h₂₅: cons₂₅ m₀) (h₂₆: cons₂₆ m₀) (h₂₇: cons₂₇ m₀) (h₂₈: cons₂₈ m₀) (h₂₉: cons₂₉ m₀) (h₃₀: cons₃₀ m₀) (h₃₁: cons₃₁ m₀) (h₃₂: cons₃₂ m₀) (h₃₃: cons₃₃ m₀) (h₃₄: cons₃₄ m₀) (h₃₅: cons₃₅ m₀) (h₃₆: cons₃₆ m₀) (h₃₇: cons₃₇ m₀) : (cons₃₈ m₀) ∧ (safe_cons₃₈ m₀) := by
  sorry
