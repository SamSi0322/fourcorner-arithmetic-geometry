import ThetaCoverClassPortable.ThetaOddNativeSquareContact
import ThetaCoverClassPortable.ThetaLineGeometricPoints

namespace FourCorner.ThetaLinesFullAssembly
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaOddNativeLineEquiv ThetaOddNativeGaloisEquiv
open ThetaOddNativeSquareContact ThetaRootCanonicalSections ThetaActualHalfCanonicalContacts
open ThetaLinesDualLines ThetaGaloisSchemeField ThetaLineGaloisAlgebra
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra ThetaDGeometricModel.K field := fieldAlgebra
local instance : IsCurveOver ThetaDGeometricModel.K field := field_isCurveOver
local instance : Algebra.EssFiniteType ThetaDGeometricModel.K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=ThetaDGeometricModel.K) (F:=field) := hasCanonicalDivisor_of_isCurveOver

/-- Identity on the SAME actual native projective dual line, using the
proved geometric equivalence of intrinsic oddness and literal contact. -/
def oddNativeActualLineEquiv : OddNativeLine ≃ ActualLine where
  toFun P := ⟨P.val,(intrinsic_odd_iff_square P.val).mp P.property⟩
  invFun P := ⟨P.val,(intrinsic_odd_iff_square P.val).mpr P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

 theorem oddNativeActualLineEquiv_galois (σ : Gal) (P : OddNativeLine) :
    oddNativeActualLineEquiv (σ • P)=σ • oddNativeActualLineEquiv P := by
  apply Subtype.ext
  rfl

def oddPicActualLineEquiv : OddPic ≃ ActualLine := oddPicLineEquiv.trans oddNativeActualLineEquiv

 theorem oddPicActualLineEquiv_galois (σ : Gal) (c : OddPic) :
    oddPicActualLineEquiv (σ • c)=σ • oddPicActualLineEquiv c := by
  change oddNativeActualLineEquiv (oddPicLineEquiv (σ • c))=_
  rw [oddPicLineEquiv_galois,oddNativeActualLineEquiv_galois]
  rfl

/-- The independently constructed actual LINE algebra is the associated
actual odd-theta algebra by its derived equivariant geometric points. -/
abbrev OddThetaAlgebra := Associated

def oddThetaGeometricPointEquiv : OddPic ≃ (OddThetaAlgebra →ₐ[ℚ] ThetaLinesAbsoluteGalois.Qbar) :=
  oddPicActualLineEquiv.trans geometricPointEquiv

 theorem oddThetaGeometricPointEquiv_galois (σ : Gal) (c : OddPic) :
    oddThetaGeometricPointEquiv (σ • c)=σ • oddThetaGeometricPointEquiv c := by
  change geometricPointEquiv (oddPicActualLineEquiv (σ • c))=_
  rw [oddPicActualLineEquiv_galois,geometricPointEquiv_absolute]
  rfl

 theorem all_square_contacts_actual_data (L : ThetaLine ThetaDGeometricModel.K) (h : IsThetaSquareContact L) :
    Nonempty (ContactData (globalSection L)) := by
  cases L with
  | affine α β => exact affine_contact_data α β h
  | vertical t => exact vertical_contact_data t h
  | yzero => exact False.elim (theta_yzero_not_bitangent ((theta_no_hyperflex .yzero).mp h))

/-- An actual bitangent is defined by the TRUE canonical divisor of the
actual natural line section; repeated-place half divisors are retained. -/
def ActualBitangent (L : ThetaLine ThetaDGeometricModel.K) : Prop :=
  ∃B : Divisor ThetaDGeometricModel.K field,0≤B ∧ Divisor.degree B=2 ∧
    canonicalDivisorOf (ThetaRootCanonicalSections.nonzero L)=(2:ℕ) • B

theorem actual_bitangent_iff_square (L : ThetaLine ThetaDGeometricModel.K) :
    ActualBitangent L ↔ IsThetaSquareContact L := by
  constructor
  · rintro ⟨B,hB,hd,hcan⟩
    exact ThetaHalfCanonicalSquareContact.half_canonical_square_contact L B hcan
  · intro h
    obtain ⟨data⟩ := all_square_contacts_actual_data L h
    exact ⟨data.divisor,data.effective,data.degree_two,data.doubled_divisor⟩

theorem actual_bitangent_iff_list (L : ThetaLine ThetaDGeometricModel.K) :
    ActualBitangent L ↔ L∈ThetaLinesProjectiveClassification.displayedList
      ThetaLinesAbsoluteGalois.r ThetaLinesAbsoluteGalois.s :=
  (actual_bitangent_iff_square L).trans (ThetaLinesProjectiveClassification.square_contact_iff_list
    ThetaLinesAbsoluteGalois.r ThetaLinesAbsoluteGalois.s
    ThetaLinesAbsoluteGalois.r_sq ThetaLinesAbsoluteGalois.s_sq L)

 theorem intrinsic_odd_native_classification (P : ThetaNativeDualCanonicalLines.NativeDual) :
    IsOddCanonicalLine P ↔ P∈actualDualLines :=
  (intrinsic_odd_iff_square P).trans (actual_dual_line_classification P)

 theorem oddPic_card : Nat.card OddPic=28 := by
  rw [Nat.card_congr oddPicActualLineEquiv,Nat.card_eq_fintype_card,actualLine_card]

def FullRadicalAction : Prop :=
  (∀er es : Bool,∃σ : Gal,
    σ ThetaLinesAbsoluteGalois.r=(if er then -ThetaLinesAbsoluteGalois.r else ThetaLinesAbsoluteGalois.r) ∧
    σ ThetaLinesAbsoluteGalois.s=(if es then -ThetaLinesAbsoluteGalois.s else ThetaLinesAbsoluteGalois.s)) ∧
  (∀σ : Gal,(σ ThetaLinesAbsoluteGalois.r=ThetaLinesAbsoluteGalois.r ∨
    σ ThetaLinesAbsoluteGalois.r= -ThetaLinesAbsoluteGalois.r) ∧
    (σ ThetaLinesAbsoluteGalois.s=ThetaLinesAbsoluteGalois.s ∨
    σ ThetaLinesAbsoluteGalois.s= -ThetaLinesAbsoluteGalois.s))

theorem full_radical_action : FullRadicalAction :=
  ⟨ThetaLinesAbsoluteGalois.absolute_independent_signs,ThetaLinesAbsoluteGalois.absolute_radical_signs⟩

/-- Full paper-scope theta-lines endpoint: complete native line locus,
28 distinct lines, two DISTINCT actual original-curve contact points and
exact actual contact divisor, genuine finite-etale odd-theta algebra with
specified 8+4+4+1 field decomposition, actual OddPic geometric points and
FULL absolute Galois action. The final list action evaluates both radicals
under the actual absolute automorphism, giving their independent signs. -/
theorem theta_lines_full :
    (∀L : ThetaLine ThetaDGeometricModel.K,ActualBitangent L ↔
      L∈ThetaLinesProjectiveClassification.displayedList ThetaLinesAbsoluteGalois.r ThetaLinesAbsoluteGalois.s) ∧
    (∀P : ThetaNativeDualCanonicalLines.NativeDual,IsOddCanonicalLine P ↔ P∈actualDualLines) ∧
    actualDualLines.Nodup ∧ actualDualLines.length=28 ∧
    (∀L : ThetaLine ThetaDGeometricModel.K,IsThetaSquareContact L → Nonempty (ContactData (globalSection L))) ∧
    Nat.card OddPic=28 ∧ Module.Finite ℚ OddThetaAlgebra ∧ Algebra.Etale ℚ OddThetaAlgebra ∧
    Nonempty (OddThetaAlgebra ≃ₐ[ℚ] ProductModel) ∧
    Nonempty (OddPic ≃ (OddThetaAlgebra →ₐ[ℚ] ThetaLinesAbsoluteGalois.Qbar)) ∧
    (∀σ : Gal,∀c : OddPic,oddThetaGeometricPointEquiv (σ • c)=σ • oddThetaGeometricPointEquiv c) ∧
    (∀σ : Gal,actualDualLines.map (dualAction σ)=
      (ThetaLinesProjectiveClassification.displayedList (σ ThetaLinesAbsoluteGalois.r)
        (σ ThetaLinesAbsoluteGalois.s)).map dualLineEquiv) ∧ FullRadicalAction :=
  ⟨actual_bitangent_iff_list,intrinsic_odd_native_classification,actualDualLines_nodup,actualDualLines_length,
    all_square_contacts_actual_data,oddPic_card,inferInstance,inferInstance,
    ⟨algebraDecomposition⟩,⟨oddThetaGeometricPointEquiv⟩,
    oddThetaGeometricPointEquiv_galois,actual_dual_absolute_action,full_radical_action⟩

#print axioms intrinsic_odd_native_classification
#print axioms oddThetaGeometricPointEquiv_galois
#print axioms theta_lines_full
end
end FourCorner.ThetaLinesFullAssembly
