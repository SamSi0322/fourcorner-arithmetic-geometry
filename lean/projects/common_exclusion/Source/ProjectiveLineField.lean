import ProjectiveLineGeometry

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.ProjectiveLineCharts
universe u
variable (K : Type u) [Field K]

abbrev zeroOpen : (P1 K).Opens := Proj.basicOpen (grading K) (MvPolynomial.X (0:Fin 2))

lemma zeroOpen_nonempty : Nonempty (zeroOpen K) :=
  Nonempty.map (chartSchemeIso K 0).inv.base inferInstance

/-- The function field of actual Proj(P1) is the original rational function field,
constructed from its genuine standard chart. -/
def fieldEquiv :
    letI := integral K
    RatFunc K ≃+* (P1 K).functionField := by
  letI := integral K
  haveI := zeroOpen_nonempty K
  have ha : IsAffineOpen (zeroOpen K) :=
    Proj.isAffineOpen_basicOpen (grading K) (MvPolynomial.X (0:Fin 2)) (member K 0) one_pos
  haveI : IsFractionRing Γ(P1 K,zeroOpen K) (P1 K).functionField :=
    functionField_isFractionRing_of_isAffineOpen (P1 K) (zeroOpen K) ha
  let e0 : chart K 0 ≃+* Γ(P1 K,zeroOpen K) :=
    (Proj.basicOpenIsoAway (grading K) (MvPolynomial.X (0:Fin 2)) (member K 0) one_pos).commRingCatIsoToRingEquiv
  let e : Polynomial K ≃+* Γ(P1 K,zeroOpen K) := (chartEquiv K 0).symm.trans e0
  exact IsFractionRing.ringEquivOfRingEquiv e

end FourCorner.ProjectiveLineCharts
#print axioms FourCorner.ProjectiveLineCharts.fieldEquiv
