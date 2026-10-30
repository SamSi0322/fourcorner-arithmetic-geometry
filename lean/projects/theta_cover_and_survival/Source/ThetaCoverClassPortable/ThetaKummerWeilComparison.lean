import ThetaCoverClassPortable.ThetaGeometricKummerLine
import ThetaCoverClassPortable.KummerWeilLocal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
namespace FourCorner.ThetaKummerWeilComparison
open ThetaDGeometricModel ThetaQQUnitRootOpens ThetaGeometricKummerLine
open ThetaCoverFunctions ThetaCoverBoundaryPoints ThetaDCanonicalInfinityDivisor
open SmoothProperClosedPointPlaces DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : Nonempty NonemptyIndex := by
  have hh : genericPoint geometricD∈⨆i,V i := by rw [ThetaGeometricKummerLine.cover];trivial
  obtain ⟨i,_⟩ := Opens.mem_iSup.mp hh
  exact ⟨i⟩

/-- Literal local Cartier equations for E-H in the original geometric
function field. Their transition ratios are actual regular units. -/
def localEquation (i : NonemptyIndex) : field := (roots i)⁻¹

theorem equation_transition (i j : NonemptyIndex) :
    localEquation i/localEquation j=
      algebraMap Γ(geometricD,V i ⊓ V j) field (cc.u i j) := by
  rw [transition_field,localEquation,localEquation,inv_div_inv]

theorem actual_Weil_order (x : closedPoints geometricD) (i : NonemptyIndex)
    (hx : x.val∈V i) :
    (boundarySum-infinitySum) (placeOfClosedPoint toBase x)=
      (placeOfClosedPoint toBase x).ord (localEquation i) := by
  let w := placeOfClosedPoint toBase x
  have hu := KummerWeilLocal.regular_unit_order toBase (V i) x hx (units i)
  rw [units_square,pow_two,w.ord_mul (mul_ne_zero (root_ne_zero i) (root_ne_zero i)) h_ne_zero,
    w.ord_mul (root_ne_zero i) (root_ne_zero i)] at hu
  have hd:=congrArg (fun Δ : Divisor K field=>Δ w) ThetaCoverDivisor.actual_divisor_h
  simp only [principalDivisor_apply,Finsupp.sub_apply,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat] at hd
  change boundarySum w-infinitySum w=w.ord ((roots i)⁻¹)
  rw [w.ord_inv]
  omega

/-- The genuine base-changed QQ line has the actual native Weil class
[E-H]. If it were trivial, the native divisor would be principal. -/
theorem geometric_line_nontrivial : ¬Nonempty (L ≅ 𝟙_ geometricD.Modules) := by
  rintro ⟨e⟩
  obtain ⟨g,_⟩ := actual_pullback_glue
  have hp : (boundarySum-infinitySum).IsPrincipal :=
    KummerWeilLocal.isPrincipal_of_trivial toBase V cc roots root_ne_zero transition_field
      ThetaGeometricKummerLine.cover (g.symm ≪≫ e) (boundarySum-infinitySum)
      (fun x i hx=>by simpa only [localEquation,Place.ord_inv] using actual_Weil_order x i hx)
  apply ThetaCoverClass.geometric_class_nonzero
  exact (QuotientAddGroup.eq_zero_iff _).mpr hp

#print axioms actual_Weil_order
#print axioms geometric_line_nontrivial
end FourCorner.ThetaKummerWeilComparison
