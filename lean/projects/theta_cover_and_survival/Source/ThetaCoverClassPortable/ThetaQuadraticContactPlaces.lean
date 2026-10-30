import ThetaCoverClassPortable.ThetaQuadraticContactScheme
import ThetaCoverClassPortable.SmoothProperRationalPointPlaces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits

namespace FourCorner.ThetaQuadraticContactPlaces
open ThetaQuadraticCurve ThetaQuadraticContactAlgebra ThetaQuadraticContactScheme
open SmoothProperClosedPointPlaces SchemePointStalkEvaluation
local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra

abbrev contactPlace (plus : Bool) : Place F functionField :=
  placeOfClosedPoint toBase (closedContact plus)

local instance (plus : Bool) : Algebra F (curve.presheaf.stalk (closedContact plus).val) :=
  stalkAlgebra toBase (closedContact plus).val

/-- Actual evaluation of the actual closed-point stalk into its degree-two
residue field; structural F-linearity is proved from the base diagram. -/
def stalkEvaluation (plus : Bool) :
    letI := stalkAlgebra toBase (closedContact plus).val
    curve.presheaf.stalk (closedContact plus).val →ₐ[F] contactField := by
  letI := stalkAlgebra toBase (closedContact plus).val
  refine {toRingHom := (Scheme.stalkClosedPointTo (contactMap plus)).hom, commutes' := ?_}
  have he : CommRingCat.ofHom (stalkBaseMap toBase (closedContact plus).val) ≫
      Scheme.stalkClosedPointTo (contactMap plus) = CommRingCat.ofHom (algebraMap F contactField) := by
    dsimp only [closedContact]
    apply Spec.map_injective
    rw [Spec.map_comp, ← fromSpecStalk_comp_base toBase, ← Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, contactMap_toBase]
  intro a
  exact congrArg (fun f => f.hom a) he

theorem stalkEvaluation_surjective (plus : Bool) :
    Function.Surjective (stalkEvaluation plus) := by
  letI := stalkAlgebra toBase (closedContact plus).val
  letI := contactMap_closedImmersion plus
  exact (ConcreteCategory.bijective_of_isIso
    (stalkClosedPointIso (.of contactField)).hom).2.comp
      ((contactMap plus).stalkMap_surjective _)

/-- The accepted stalk/valuation-ring equivalence is used over F itself. -/
def valuationEvaluation (plus : Bool) : (contactPlace plus).toValuationSubring →ₐ[F] contactField :=
  (stalkEvaluation plus).comp
    (SmoothProperRationalPointPlaces.stalkValuationAlgEquiv toBase (closedContact plus)).symm.toAlgHom

theorem valuationEvaluation_surjective (plus : Bool) :
    Function.Surjective (valuationEvaluation plus) :=
  (stalkEvaluation_surjective plus).comp
    (SmoothProperRationalPointPlaces.stalkValuationAlgEquiv toBase (closedContact plus)).symm.surjective

theorem valuationEvaluation_kernel (plus : Bool) :
    RingHom.ker (valuationEvaluation plus).toRingHom =
      IsLocalRing.maximalIdeal (contactPlace plus).toValuationSubring :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective
    (valuationEvaluation plus).toRingHom (valuationEvaluation_surjective plus))

def residueEvaluation (plus : Bool) : (contactPlace plus).ResidueField →ₐ[F] contactField :=
  Ideal.Quotient.liftₐ _ (valuationEvaluation plus) (by
    rw [← valuationEvaluation_kernel]
    exact fun _ hx => hx)

theorem residueEvaluation_surjective (plus : Bool) :
    Function.Surjective (residueEvaluation plus) := by
  intro a
  obtain ⟨z,hz⟩ := valuationEvaluation_surjective plus a
  exact ⟨IsLocalRing.residue _ z,hz⟩

/-- This is the genuine residue field of the native place, with its true
F-algebra structure, rather than an assigned numerical degree. -/
def contactResidueEquiv (plus : Bool) : (contactPlace plus).ResidueField ≃ₐ[F] contactField :=
  AlgEquiv.ofBijective (residueEvaluation plus)
    ⟨(residueEvaluation plus).injective,residueEvaluation_surjective plus⟩

theorem contactPlace_degree (plus : Bool) : (contactPlace plus).deg=2 := by
  change Module.finrank F (contactPlace plus).ResidueField=2
  rw [(contactResidueEquiv plus).toLinearEquiv.finrank_eq]
  exact contact_degree

/-- Native Weil cycles of the actual closed quadratic contacts. Each is
ONE closed point of residue degree two, not two asserted rational points. -/
def contactDivisor (plus : Bool) : Divisor F functionField := Finsupp.single (contactPlace plus) 1
abbrev Bplus2 := contactDivisor true
abbrev Bminus2 := contactDivisor false

theorem contactDivisor_effective (plus : Bool) : 0 ≤ contactDivisor plus := by
  classical
  intro w
  simp only [contactDivisor,Finsupp.single_apply,Finsupp.zero_apply]
  split_ifs <;> norm_num
theorem contactDivisor_degree (plus : Bool) : Divisor.degree (contactDivisor plus)=2 := by
  rw [contactDivisor,Divisor.degree_single,contactPlace_degree]
  norm_num

def contactDifference : Divisor.degZero (K:=F) (F:=functionField) :=
  ⟨Bplus2-Bminus2,by
    rw [Divisor.mem_degZero,map_sub,contactDivisor_degree,contactDivisor_degree]
    norm_num⟩

/-- An actual native Pic0 class over F; comparison with the cover class and
constant-field scalar extension are separate theorems, not definition data. -/
def contactClass : Pic0 F functionField := Pic0.mk contactDifference

end FourCorner.ThetaQuadraticContactPlaces
