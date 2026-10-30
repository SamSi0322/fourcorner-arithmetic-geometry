import ThetaCoverClassPortable.ThetaOddNativeLineEquiv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve KaehlerDifferential
namespace FourCorner.ThetaOddNativeGaloisEquiv
open ThetaDGeometricModel ThetaGaloisSchemeField ThetaGaloisFieldAction ThetaGaloisCanonicalPlane
open ThetaGaloisCanonicalCorrespondence ThetaNativeDualCanonicalLines ThetaOddNativeLineEquiv
open ThetaOddThetaCanonicalLines ThetaActualOddThetaClasses DivisorPicClassification SemilinearPicAndEll
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀v : Place K field,v.DCoordGenerates := dCoordGenerates_of_isCurveOver

 def oddPicMap (σ : Gal) (c : OddPic) : OddPic := ⟨picMap σ c.val,picMap_odd σ c.property⟩

 theorem native_dualAction_one (P : NativeDual) : ThetaLinesDualLines.dualAction (1:Gal) P=P := by
  obtain ⟨L,rfl⟩ := ThetaLinesDualLines.dualLineEquiv.surjective P
  rw [ThetaLinesDualLines.dualAction_line]
  congr 1
  cases L <;> rfl

 theorem native_dualAction_mul (σ ρ : Gal) (P : NativeDual) :
    ThetaLinesDualLines.dualAction (σ*ρ) P=
      ThetaLinesDualLines.dualAction σ (ThetaLinesDualLines.dualAction ρ P) := by
  obtain ⟨L,rfl⟩ := ThetaLinesDualLines.dualLineEquiv.surjective P
  rw [ThetaLinesDualLines.dualAction_line,ThetaLinesDualLines.dualAction_line,
    ThetaLinesDualLines.dualAction_line]
  congr 1
  cases L <;> rfl

 theorem odd_line_preserved (σ : Gal) {L : NativeDual} (h : IsOddCanonicalLine L) :
    IsOddCanonicalLine (ThetaLinesDualLines.dualAction σ L) := by
  obtain ⟨a,ha,B,hL,hB,hell,hcan⟩ := h
  refine ⟨coefficientMap σ a,coefficientMap_ne_zero σ ha,absoluteAction σ • B,
    ?_,smul_effective _ hB,?_,?_⟩
  · rw [hL,pure_dualAction_dualOf]
  · rwa [ell_smul]
  · calc
      _=absoluteAction σ • canonicalDivisorOf (planeToField_ne_zero ha) :=
        canonical_plane_divisor_transport σ ha
      _=absoluteAction σ • ((2:ℕ) • B) := congrArg (fun E:ActualDivisor=>absoluteAction σ • E) hcan
      _=(2:ℕ) • (absoluteAction σ • B) := by simp only [two_nsmul,smul_add]

 def oddLineMap (σ : Gal) (L : OddNativeLine) : OddNativeLine :=
  ⟨ThetaLinesDualLines.dualAction σ L.val,odd_line_preserved σ L.property⟩

instance oddPicAction : MulAction Gal OddPic where
  smul := oddPicMap
  one_smul c := Subtype.ext (picMap_one c.val)
  mul_smul σ ρ c := Subtype.ext (picMap_mul σ ρ c.val)
instance oddNativeLineAction : MulAction Gal OddNativeLine where
  smul := oddLineMap
  one_smul L := Subtype.ext (native_dualAction_one L.val)
  mul_smul σ ρ L := Subtype.ext (native_dualAction_mul σ ρ L.val)

/-- The ACTUAL absolute-Galois equivalence with native projectivized linear
forms in the intrinsic odd-canonical locus. No presumed Pic/line or Galois
identification occurs; scalar-choice independence follows from true divisors. -/
theorem oddPicLineEquiv_galois (σ : Gal) (c : OddPic) :
    oddPicLineEquiv (σ • c)=σ • oddPicLineEquiv c := by
  have hnew : CanonicalRepresentative (picMap σ c.val)
      (chosenB (oddPicMap σ c)) (chosenCoefficients (oddPicMap σ c)) :=
    chosenRepresentative (oddPicMap σ c)
  obtain ⟨-,u,hu,hcoeff⟩ := reverse_classification_equivariant σ c.property
    (chosenRepresentative c) hnew
  apply Subtype.ext
  change dualOf (chosenCoefficients (oddPicMap σ c)) (chosenNonzero (oddPicMap σ c))=
    ThetaLinesDualLines.dualAction σ (dualOf (chosenCoefficients c) (chosenNonzero c))
  rw [pure_dualAction_dualOf]
  exact dual_eq_of_scalar (chosenNonzero (oddPicMap σ c))
    (coefficientMap_ne_zero σ (chosenNonzero c)) u hcoeff.symm

#print axioms odd_line_preserved
#print axioms oddPicLineEquiv_galois
end FourCorner.ThetaOddNativeGaloisEquiv
