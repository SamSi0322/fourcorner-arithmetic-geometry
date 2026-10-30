import ThetaCoverClassPortable.ThetaQuadraticCartierBaseChange
import ThetaCoverClassPortable.ThetaQQCoverLineEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TopologicalSpace AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace FourCorner.ThetaQuadraticCartierWeilNative
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticCartierBaseChange
open ThetaQuadraticBoundary ThetaQuadraticInfinityScheme ThetaQuadraticHalfDivisor
open SmoothProperClosedPointPlaces ThetaQQUnitRootOpens DivisorPicClassification
local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := fieldAlgebra
local instance : IsCurveOver F functionField := field_isCurveOver
local instance : Algebra.EssFiniteType F functionField := field_essFiniteType
local instance : Nonempty NonemptyIndex := by
  have h : genericPoint curve∈⨆i,V i := by rw [ThetaQuadraticCartierBaseChange.cover];trivial
  obtain ⟨i,_⟩ := Opens.mem_iSup.mp h
  exact ⟨i⟩

def localEquation (i : NonemptyIndex) : functionField := (roots i)⁻¹

theorem equation_transition (i j : NonemptyIndex) :
    localEquation i/localEquation j=
      algebraMap Γ(curve,V i ⊓ V j) functionField (cc.u i j) := by
  rw [transition_field,localEquation,localEquation,inv_div_inv]

/-- Genuine Cartier-to-Weil coefficients of the actual pullback of the
frozen QQ line, at every native closed point of D_F. -/
theorem actual_Weil_order (x : closedPoints curve) (i : NonemptyIndex) (hx : x.val∈V i) :
    (E2-H2) (placeOfClosedPoint toBase x)=
      (placeOfClosedPoint toBase x).ord (localEquation i) := by
  let w := placeOfClosedPoint toBase x
  have hu := KummerWeilLocal.regular_unit_order toBase (V i) x hx (units i)
  rw [units_square,pow_two,w.ord_mul (mul_ne_zero (root_ne_zero i) (root_ne_zero i)) h2_ne_zero,
    w.ord_mul (root_ne_zero i) (root_ne_zero i)] at hu
  have hd := congrArg (fun D : Divisor F functionField => D w)
    ThetaQuadraticNativeDivisorIdentities.actual_divisor_h2
  simp only [principalDivisor_apply,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat] at hd
  change (E2-H2) w=w.ord ((roots i)⁻¹)
  rw [w.ord_inv]
  omega

theorem line_nontrivial : ¬Nonempty (L ≅ 𝟙_ curve.Modules) := by
  rintro ⟨e⟩
  obtain ⟨g,_⟩ := actual_pullback_glue
  have hp : (E2-H2).IsPrincipal :=
    KummerWeilLocal.isPrincipal_of_trivial toBase V cc roots root_ne_zero transition_field
      ThetaQuadraticCartierBaseChange.cover (g.symm ≪≫ e) (E2-H2)
      (fun x i hx=>by simpa only [localEquation,Place.ord_inv] using actual_Weil_order x i hx)
  apply half_not_principal
  rwa [ThetaQuadraticNativeDivisorIdentities.halfDivisor_eq]

theorem line_invertible : Scheme.Modules.IsInvertible L := ThetaQQKummerLine.L_invertible.pullback _

theorem line_square_trivial : Nonempty (L ⊗ L ≅ 𝟙_ curve.Modules) := by
  obtain ⟨e,_⟩ := ThetaQQKummerLine.square_trivialization
  exact ⟨Functor.Monoidal.μIso (Scheme.Modules.pullback toRational) ThetaQQKummerLine.L ThetaQQKummerLine.L ≪≫
    (Scheme.Modules.pullback toRational).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso toRational⟩

/-- Actual compatibility of successive QQ -> F -> Qbar pullbacks. -/
def geometric_pullback_iso : (Scheme.Modules.pullback geometricProjection).obj L ≅
    ThetaGeometricKummerLine.L :=
  (Scheme.Modules.pullbackComp geometricProjection toRational).app ThetaQQKummerLine.L ≪≫
    (Scheme.Modules.pullbackCongr geometricProjection_toRational).app ThetaQQKummerLine.L

abbrev origin := ThetaQQRigidifiedLine.origin
abbrev sectionF := RelPicard.rigSection (ThetaLiteralModels.dToBase ℚ) baseMap origin

theorem sectionF_original : sectionF ≫ toRational=baseMap ≫ origin.val := by
  simp only [sectionF,RelPicard.rigSection,toRational,pullback.lift_fst]

def rigidifiedLine : RelPicard.RigidifiedLineBundle (ThetaLiteralModels.dToBase ℚ) origin baseMap where
  L := L
  isInvertible := line_invertible
  rigidified := ⟨(Scheme.Modules.pullbackComp sectionF toRational).app ThetaQQKummerLine.L ≪≫
    (Scheme.Modules.pullbackCongr sectionF_original).app ThetaQQKummerLine.L ≪≫
    ((Scheme.Modules.pullbackComp baseMap origin.val).app ThetaQQKummerLine.L).symm ≪≫
    (Scheme.Modules.pullback baseMap).mapIso ThetaQQRigidifiedLine.originFiberBasis ≪≫
    Scheme.Modules.pullbackUnitIso baseMap⟩

def rationalPicardClass : RelPicard.RigidifiedLineBundle.Classes
    (ThetaLiteralModels.dToBase ℚ) origin baseMap := Quotient.mk _ rigidifiedLine

def unitPicardClass : RelPicard.RigidifiedLineBundle.Classes
    (ThetaLiteralModels.dToBase ℚ) origin baseMap :=
  Quotient.mk _ (RelPicard.RigidifiedLineBundle.unit _)

theorem rationalPicardClass_ne_unit : rationalPicardClass≠unitPicardClass := by
  intro h
  exact line_nontrivial (Quotient.exact h)

/-- Actual constant-field extension of the effective QQ cover line,
with its native Cartier-Weil class and genuine relative-Picard object.
The represented Jacobian interface is deliberately a further endpoint. -/
theorem actual_quadratic_cover_line :
    Scheme.Modules.IsInvertible L ∧ Nonempty (L ⊗ L ≅ 𝟙_ curve.Modules) ∧
    (¬Nonempty (L ≅ 𝟙_ curve.Modules)) ∧ rationalPicardClass≠unitPicardClass ∧
    Nonempty ((Scheme.Modules.pullback geometricProjection).obj L ≅ ThetaGeometricKummerLine.L) ∧
    ∀ (x : closedPoints curve) (i : NonemptyIndex),x.val∈V i →
      (E2-H2) (placeOfClosedPoint toBase x)=(placeOfClosedPoint toBase x).ord (localEquation i) :=
  ⟨line_invertible,line_square_trivial,line_nontrivial,rationalPicardClass_ne_unit,
    ⟨geometric_pullback_iso⟩,actual_Weil_order⟩

end FourCorner.ThetaQuadraticCartierWeilNative
