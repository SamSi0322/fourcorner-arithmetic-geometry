import ThetaCoverClassPortable.ThetaQuadraticInfinityQQ

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits

namespace FourCorner.ActualClosedPointNativePlace
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} (c : X ⟶ Spec (.of K)) [IsIntegral X]
  [SmoothOfRelativeDimension 1 c] [IsProper c]
  (j : Spec (.of L) ⟶ X) [IsClosedImmersion j]
  (h_over : j ≫ c=Spec.map (CommRingCat.ofHom (algebraMap K L)))

def actualPoint : closedPoints X :=
  ⟨j (IsLocalRing.closedPoint L),by
    have h := j.isClosedEmbedding.isClosedMap _
      (isClosed_singleton : IsClosed ({IsLocalRing.closedPoint L} : Set (Spec (.of L))))
    simpa using h⟩

abbrev nativeAlgebra : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
abbrev nativePlace : letI := nativeAlgebra c; Place K X.functionField := by
  letI := nativeAlgebra c
  exact SmoothProperClosedPointPlaces.placeOfClosedPoint c (actualPoint j)

def stalkEvaluation :
    letI := SchemePointStalkEvaluation.stalkAlgebra c (actualPoint j).val
    X.presheaf.stalk (actualPoint j).val →ₐ[K] L := by
  letI := SchemePointStalkEvaluation.stalkAlgebra c (actualPoint j).val
  refine {toRingHom := (Scheme.stalkClosedPointTo j).hom,commutes' := ?_}
  have he : CommRingCat.ofHom (SchemePointStalkEvaluation.stalkBaseMap c (actualPoint j).val) ≫
      Scheme.stalkClosedPointTo j=CommRingCat.ofHom (algebraMap K L) := by
    dsimp only [actualPoint]
    apply Spec.map_injective
    rw [Spec.map_comp,←SchemePointStalkEvaluation.fromSpecStalk_comp_base c,
      ←Category.assoc,Scheme.Spec_stalkClosedPointTo_fromSpecStalk,h_over]
  intro a
  exact congrArg (fun f => f.hom a) he

theorem stalkEvaluation_surjective :
    letI := SchemePointStalkEvaluation.stalkAlgebra c (actualPoint j).val
    Function.Surjective (stalkEvaluation c j h_over) := by
  letI := SchemePointStalkEvaluation.stalkAlgebra c (actualPoint j).val
  exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of L)).hom).2.comp
    (j.stalkMap_surjective _)

def valuationEvaluation :
    letI := nativeAlgebra c
    (nativePlace c j).toValuationSubring →ₐ[K] L := by
  letI := nativeAlgebra c
  letI := SchemePointStalkEvaluation.stalkAlgebra c (actualPoint j).val
  exact (stalkEvaluation c j h_over).comp
    (SmoothProperRationalPointPlaces.stalkValuationAlgEquiv c (actualPoint j)).symm.toAlgHom

theorem valuationEvaluation_surjective :
    letI := nativeAlgebra c
    Function.Surjective (valuationEvaluation c j h_over) := by
  letI := nativeAlgebra c
  letI := SchemePointStalkEvaluation.stalkAlgebra c (actualPoint j).val
  exact (stalkEvaluation_surjective c j h_over).comp
    (SmoothProperRationalPointPlaces.stalkValuationAlgEquiv c (actualPoint j)).symm.surjective

theorem valuationEvaluation_kernel :
    letI := nativeAlgebra c
    RingHom.ker (valuationEvaluation c j h_over).toRingHom=
    IsLocalRing.maximalIdeal (nativePlace c j).toValuationSubring := by
  letI := nativeAlgebra c
  exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective
    (valuationEvaluation c j h_over).toRingHom (valuationEvaluation_surjective c j h_over))

def residueEvaluation :
    letI := nativeAlgebra c
    (nativePlace c j).ResidueField →ₐ[K] L := by
  letI := nativeAlgebra c
  exact Ideal.Quotient.liftₐ _ (valuationEvaluation c j h_over) (by
    rw [←valuationEvaluation_kernel c j h_over]
    exact fun _ hx => hx)

def residueEquiv :
    letI := nativeAlgebra c
    (nativePlace c j).ResidueField ≃ₐ[K] L := by
  letI := nativeAlgebra c
  exact AlgEquiv.ofBijective (residueEvaluation c j h_over) ⟨(residueEvaluation c j h_over).injective,by
    intro a
    obtain ⟨z,hz⟩ := valuationEvaluation_surjective c j h_over a
    exact ⟨IsLocalRing.residue _ z,hz⟩⟩

include h_over in
theorem nativePlace_degree :
    letI := nativeAlgebra c
    (nativePlace c j).deg=Module.finrank K L := by
  letI := nativeAlgebra c
  change Module.finrank K (nativePlace c j).ResidueField=Module.finrank K L
  exact (residueEquiv c j h_over).toLinearEquiv.finrank_eq

def cycle : letI := nativeAlgebra c; Divisor K X.functionField := by
  letI := nativeAlgebra c
  exact Finsupp.single (nativePlace c j) 1
theorem cycle_effective : letI := nativeAlgebra c; 0≤cycle c j := by
  letI := nativeAlgebra c
  exact Finsupp.single_nonneg.mpr (by norm_num)
include h_over in
theorem cycle_degree :
    letI := nativeAlgebra c
    Divisor.degree (cycle c j)=(Module.finrank K L:ℤ) := by
  letI := nativeAlgebra c
  rw [cycle,Divisor.degree_single,nativePlace_degree c j h_over]
  simp

end FourCorner.ActualClosedPointNativePlace
