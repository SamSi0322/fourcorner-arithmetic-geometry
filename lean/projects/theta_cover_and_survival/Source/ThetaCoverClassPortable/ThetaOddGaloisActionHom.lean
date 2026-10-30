import ThetaCoverClassPortable.ThetaOddNativeGaloisEquiv
import Mathlib.GroupTheory.GroupAction.Hom

noncomputable section
set_option autoImplicit false
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaOddGaloisActionHom
open ThetaDGeometricModel ThetaGaloisSchemeField ThetaOddNativeLineEquiv ThetaOddNativeGaloisEquiv
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver

def toNativeLine : OddPic →[Gal] OddNativeLine where
  toFun := oddPicLineEquiv
  map_smul' := oddPicLineEquiv_galois

def toOddPic : OddNativeLine →[Gal] OddPic where
  toFun := oddPicLineEquiv.symm
  map_smul' σ L := by
    apply oddPicLineEquiv.injective
    rw [oddPicLineEquiv.apply_symm_apply,oddPicLineEquiv_galois,oddPicLineEquiv.apply_symm_apply]
    rfl

 theorem both_inverse_pic (c : OddPic) : toOddPic (toNativeLine c)=c :=
  oddPicLineEquiv.symm_apply_apply c
 theorem both_inverse_line (L : OddNativeLine) : toNativeLine (toOddPic L)=L :=
  oddPicLineEquiv.apply_symm_apply L

#print axioms toNativeLine
#print axioms toOddPic
#print axioms both_inverse_pic
#print axioms both_inverse_line
end FourCorner.ThetaOddGaloisActionHom
