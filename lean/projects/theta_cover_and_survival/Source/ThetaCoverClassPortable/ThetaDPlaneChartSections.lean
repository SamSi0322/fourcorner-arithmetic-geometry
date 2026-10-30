import ThetaCoverClassPortable.ThetaDGeometricChartPoints
import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf

namespace FourCorner.ThetaDPlaneChartSections
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

 theorem original_integral : IsIntegral (D ℚ) := by
  letI := ThetaSourceComparison.source_integral
  letI := ThetaProjectionDegree.projection_surjective
  letI := ThetaProjectionFiniteEtale.projection_etale
  exact ThetaFlatIntegralDescent.integral projection

local instance : IsIntegral (D ℚ) := original_integral
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra

abbrev chartRing (j : Fin 3) := affineRing (targetEquation ℚ) j
def chartMap (j : Fin 3) : Spec (.of (chartRing j)) ⟶ D ℚ :=
  (chartIso (targetEquation ℚ) (target_homogeneous ℚ) j).inv ≫
    (Proj.basicOpen (grading (targetEquation ℚ) (target_homogeneous ℚ))
      (coordinate (targetEquation ℚ) (target_homogeneous ℚ) j)).ι
local instance (j : Fin 3) : IsOpenImmersion (chartMap j) := by unfold chartMap;infer_instance

def U (j : Fin 3) : (D ℚ).Opens := chartMap j ''ᵁ ⊤
def geoU (j : Fin 3) : geometricD.Opens := pullback.fst (dToBase ℚ) qb ⁻¹ᵁ U j

theorem affine_U (j : Fin 3) : IsAffineOpen (U j) := by
  rw [U,Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange (chartMap j)

theorem affine_geoU (j : Fin 3) : IsAffineOpen (geoU j) := by
  let e := P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.pullbackAffineOpenIsoSpecTensor
    (dToBase ℚ) K (U j) (affine_U j)
  exact IsAffine.of_isIso e.hom

/-- The original Proj chart quotient and its ACTUAL structure-sheaf sections. -/
def sectionsRingEquiv (j : Fin 3) : Γ(D ℚ,U j) ≃+* chartRing j :=
  ((chartMap j).appIso ⊤ ≪≫ Scheme.ΓSpecIso (.of (chartRing j))).commRingCatIsoToRingEquiv

local instance originalSectionsAlgebra (j : Fin 3) : Algebra ℚ Γ(D ℚ,U j) :=
  Scheme.TwoAffineOpenCover.algebraOfHom (dToBase ℚ) (U j)
local instance geoSectionsAlgebra (j : Fin 3) : Algebra K Γ(geometricD,geoU j) :=
  Scheme.TwoAffineOpenCover.algebraOfHom toBase (geoU j)

def sectionsAlgEquiv (j : Fin 3) : Γ(D ℚ,U j) ≃ₐ[ℚ] chartRing j :=
  AlgEquiv.ofRingEquiv (f:=sectionsRingEquiv j) (by
    intro q
    exact RingHom.congr_fun (Subsingleton.elim
      ((sectionsRingEquiv j).toRingHom.comp (algebraMap ℚ Γ(D ℚ,U j)))
      (algebraMap ℚ (chartRing j))) q)

 def tensorSectionsEquiv (j : Fin 3) : (K ⊗[ℚ] chartRing j) ≃ₐ[K] (K ⊗[ℚ] Γ(D ℚ,U j)) :=
  { (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[ℚ] K) (sectionsAlgEquiv j).symm).toRingEquiv with
    commutes' := by intro k;simp [Algebra.TensorProduct.algebraMap_apply] }

/-- Explicit structural-K comparison of actual base-changed affine
sections with the literal tensor of the ORIGINAL rational chart quotient. -/
def actualChartEquiv (j : Fin 3) : (K ⊗[ℚ] chartRing j) ≃ₐ[K] Γ(geometricD,geoU j) :=
  (tensorSectionsEquiv j).trans
    (P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv
      (dToBase ℚ) K (U j) (affine_U j))

#print axioms original_integral
#print axioms sectionsAlgEquiv
#print axioms actualChartEquiv
end
end FourCorner.ThetaDPlaneChartSections
