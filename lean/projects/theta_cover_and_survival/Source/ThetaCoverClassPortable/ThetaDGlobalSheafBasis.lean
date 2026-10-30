import ThetaCoverClassPortable.ThetaDCanonicalPlaneBasis

namespace FourCorner.ThetaDGlobalSheafBasis
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates ThetaDProjectiveInfinityCover
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType

 theorem geometric_separated : geometricD.IsSeparated := by
  constructor
  rw [←terminal.comp_from toBase]
  infer_instance
local instance : geometricD.IsSeparated := geometric_separated

/-- An actual plane-chart cover of the SAME geometric original D. -/
def planeCover : geometricD.TwoAffineOpenCover where
  U0 := geoU 0
  U1 := geoU 2
  isAffineOpen_U0 := affine_geoU 0
  isAffineOpen_U1 := affine_geoU 2
  sup_eq_top := geometric_XZ_cover
  isAffineOpen_inf := (affine_geoU 0).inf (affine_geoU 2)
local instance : Nonempty planeCover.U0 := geoU_nonempty 0
local instance : Nonempty planeCover.U1 := geoU_nonempty 2
local instance : Module K Γ(toBase.kaehler,⊤) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤

/-- True global relative Kahler sections and the actual native rational
regular differentials, linked by the existing genuine sheaf/local-to-field
comparison theorem on this actual plane cover. -/
def globalEquiv : Γ(toBase.kaehler,⊤) ≃ₗ[K] regularDifferentials K field := by
  let e₀ := Classical.choice (KaehlerSheafBridge.exists_globalSectionsEquivChartH0 toBase planeCover)
  let e₁ := Classical.choose (planeCover.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField toBase)
  exact e₀.trans e₁

/-- The actual global Kahler sheaf has the plane canonical basis, transferred
through a PROVED actual sheaf/function-field equivalence. -/
def basis : Module.Basis (Fin 3) K Γ(toBase.kaehler,⊤) :=
  ThetaDCanonicalPlaneBasis.basis.map globalEquiv.symm

 theorem basis_as_rational_differentials (i : Fin 3) :
    globalEquiv (basis i)=ThetaDCanonicalPlaneBasis.forms i := by
  simp only [basis,Module.Basis.map_apply,LinearEquiv.apply_symm_apply]
  exact congrFun ThetaDCanonicalPlaneBasis.basis_eq_forms i

#print axioms planeCover
#print axioms globalEquiv
#print axioms basis
#print axioms basis_as_rational_differentials
end
end FourCorner.ThetaDGlobalSheafBasis
