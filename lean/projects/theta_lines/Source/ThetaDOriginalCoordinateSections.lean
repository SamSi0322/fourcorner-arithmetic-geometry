import ThetaDGlobalSheafBasis
import Mathlib.LinearAlgebra.Matrix.Dual

namespace FourCorner.ThetaDOriginalCoordinateSections
open AlgebraicGeometry AlgebraicCurve
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDActualDifferential
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : Module K Γ(toBase.kaehler,⊤) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤

/-- The rational cyclic permutation matching original [X:Y:Z], rather
than the construction order [1:x:y]. -/
def coordinateCycle : Equiv.Perm (Fin 3) where
  toFun := ![1,2,0]
  invFun := ![2,0,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Actual regular differentials in the ORIGINAL coordinate order X,Y,Z. -/
def originalBasis : Module.Basis (Fin 3) K (regularDifferentials K field) :=
  ThetaDCanonicalPlaneBasis.basis.reindex coordinateCycle.symm

 theorem originalBasis_values (i : Fin 3) :
    (originalBasis i : Ω[field⁄K])=![x • omega,y • omega,omega] i := by
  simp only [originalBasis,Module.Basis.reindex_apply,Equiv.symm_symm]
  rw [congrFun ThetaDCanonicalPlaneBasis.basis_eq_forms]
  fin_cases i <;> rfl

/-- The ACTUAL native dual plane's linear forms correspond to the actual
canonical regular-differential space; the coordinate convention is explicit. -/
def planeFormEquiv : Module.Dual K (Fin 3 → K) ≃ₗ[K] regularDifferentials K field :=
  (dotProductEquiv K (Fin 3)).symm.trans originalBasis.equivFun.symm

/-- Genuine global relative Kahler sections, via the proved geometric
sheaf/function-field comparison. No Picard or Galois identification is assumed. -/
def planeGlobalSectionEquiv : Module.Dual K (Fin 3 → K) ≃ₗ[K] Γ(toBase.kaehler,⊤) :=
  planeFormEquiv.trans ThetaDGlobalSheafBasis.globalEquiv.symm

 theorem planeForm_formula (a : Fin 3 → K) :
    (planeFormEquiv (dotProductEquiv K (Fin 3) a) : Ω[field⁄K])=
      (algebraMap K field (a 2)+algebraMap K field (a 0)*x+
        algebraMap K field (a 1)*y) • omega := by
  simp only [planeFormEquiv,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  change (originalBasis.equivFun.symm a : Ω[field⁄K])=_
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Fin.sum_univ_three,Submodule.coe_add,Submodule.coe_smul,originalBasis_values]
  change a 0 • (x • omega)+a 1 • (y • omega)+a 2 • omega=_
  rw [algebra_compatible_smul field (a 0) (x • omega),
    algebra_compatible_smul field (a 1) (y • omega),
    algebra_compatible_smul field (a 2) omega,smul_smul,smul_smul]
  simp only [add_smul]
  abel

/-- In particular the original line aX+bY+cZ maps to (c+a*x+b*y)omega.
This is the exact native dotProductEquiv used by the frozen parent dualLine. -/
theorem original_line_section (a b c : K) :
    (planeFormEquiv (dotProductEquiv K (Fin 3) ![a,b,c]) : Ω[field⁄K])=
      (algebraMap K field c+algebraMap K field a*x+algebraMap K field b*y) • omega :=
  planeForm_formula ![a,b,c]

#print axioms originalBasis_values
#print axioms planeFormEquiv
#print axioms planeGlobalSectionEquiv
#print axioms planeForm_formula
#print axioms original_line_section
end
end FourCorner.ThetaDOriginalCoordinateSections
