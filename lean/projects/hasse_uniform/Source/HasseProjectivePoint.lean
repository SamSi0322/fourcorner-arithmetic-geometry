import HasseRationalSource
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! Actual projective rational points of the three displayed homogeneous quadrics.
The standard projectivization is the quotient by Q× scaling; no point existence
or local-global implication is inserted into the definitions. -/
namespace FourCorner.HasseProjectivePoint

open HasseRationalSource CompleteSource11

abbrev P4 := Projectivization ℚ (Fin 5 → ℚ)

/-- Literal rational projective C_p, including all coordinate hyperplanes.
Equations are required on some nonzero representative of the projective point. -/
def OnCurve (p : ℚ) (x : P4) : Prop :=
  ∃ (v : Fin 5 → ℚ) (hv : v ≠ 0), Projectivization.mk ℚ v hv=x ∧
    Source p (v 0) (v 1) (v 2) (v 3) (v 4)

def RationalPoint (p : ℚ) := {x : P4 // OnCurve p x}

/-- The displayed quadrics are genuinely homogeneous, with common degree two. -/
theorem source_scale (p : ℚ) (v : Fin 5 → ℚ) (c : ℚ)
    (h : Source p (v 0) (v 1) (v 2) (v 3) (v 4)) :
    Source p ((c • v) 0) ((c • v) 1) ((c • v) 2) ((c • v) 3) ((c • v) 4) := by
  change Source p (c*v 0) (c*v 1) (c*v 2) (c*v 3) (c*v 4)
  rcases h with ⟨hV,hW,hT⟩
  refine ⟨?_,?_,?_⟩
  · linear_combination c^2*hV
  · linear_combination c^2*hW
  · linear_combination c^2*hT

/-- Defining the curve with an existential representative agrees exactly with
testing the equations on Mathlib's chosen representative. -/
theorem onCurve_iff_rep (p : ℚ) (x : P4) :
    OnCurve p x ↔ Source p (x.rep 0) (x.rep 1) (x.rep 2) (x.rep 3) (x.rep 4) := by
  constructor
  · rintro ⟨v,hv,hx,h⟩
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℚ v hv
    rw [hx] at ha
    rw [← ha]
    exact source_scale p v a h
  · intro h
    exact ⟨x.rep,x.rep_nonzero,Projectivization.mk_rep x,h⟩

/-- A true projective rational point supplies a nonzero full homogeneous tuple. -/
noncomputable def toHomogeneousPoint (p : ℚ) (P : RationalPoint p) : HomogeneousPoint p where
  Z := P.val.rep 0
  U := P.val.rep 1
  V := P.val.rep 2
  W := P.val.rep 3
  T := P.val.rep 4
  equations := (onCurve_iff_rep p P.val).mp P.property
  nonzero := by
    rintro ⟨hz,hu,hv,hw,ht⟩
    apply P.val.rep_nonzero
    funext i
    fin_cases i <;> assumption

/-- Every nonzero tuple gives its genuine Q× equivalence class in P4. -/
def ofHomogeneousPoint (p : ℚ) (P : HomogeneousPoint p) : RationalPoint p := by
  let v : Fin 5 → ℚ := ![P.Z,P.U,P.V,P.W,P.T]
  have hv : v ≠ 0 := by
    intro hh
    apply P.nonzero
    exact ⟨congrFun hh 0,congrFun hh 1,congrFun hh 2,congrFun hh 3,congrFun hh 4⟩
  exact ⟨Projectivization.mk ℚ v hv,v,hv,rfl,P.equations⟩

/-- Boundary-complete projective-point existence is equivalent to the strict
finite-rho four-square source under exactly p>1. -/
theorem rationalPoint_nonempty_iff_localPoint (p : ℚ) (hp : 1<p) :
    Nonempty (RationalPoint p) ↔ Nonempty (HasseNorms.LocalPoint ℚ p) := by
  rw [← homogeneous_nonempty_iff_localPoint p hp]
  exact ⟨fun ⟨P⟩ => ⟨toHomogeneousPoint p P⟩,
    fun ⟨P⟩ => ⟨ofHomogeneousPoint p P⟩⟩

theorem rationalPoint_nonempty_iff_literal_squares (p : ℚ) (hp : 1<p) :
    Nonempty (RationalPoint p) ↔ HasseNormsInterface.LocalSquares ℚ p := by
  rw [rationalPoint_nonempty_iff_localPoint p hp,
    HasseNormsInterface.localPoint_iff_localSquares]

#print axioms source_scale
#print axioms onCurve_iff_rep
#print axioms toHomogeneousPoint
#print axioms ofHomogeneousPoint
#print axioms rationalPoint_nonempty_iff_localPoint
#print axioms rationalPoint_nonempty_iff_literal_squares

end FourCorner.HasseProjectivePoint
