import AffineChartPlaceEvaluation

noncomputable section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.FixedAffinePointEvaluation
open AffineChartPlaceEvaluation SmoothProperPointPlaceTransport SmoothProperRationalPointPlaces
variable {K F G:Type u} [Field K] [Field F] [Field G] [Algebra K F] [Algebra K G]

/-- Residue evaluation is preserved through the GIVEN field map and the
GIVEN equality of actual places, for the same original field element. -/
theorem evaluate_congr_of_eq (e:F≃ₐ[K]G) (v:Place K F) (hv:v.IsRational)
    (w:Place K G) (hw:w.IsRational)
    (hvw:Place.congrEquiv e.toRingEquiv e.commutes v=w)
    (x:v.toValuationSubring) (y:w.toValuationSubring) (hxy:(y:G)=e (x:F)) :
    ResiduePlaceEvaluation.evaluate w hw y=ResiduePlaceEvaluation.evaluate v hv x := by
  subst w
  have hy:y=placeValuationAlgEquiv e v x := Subtype.ext hxy
  rw [hy]
  exact evaluate_congr e v hv hw x

variable {R:Type u} [CommRing R] [IsDomain R] [Algebra K R]
    {X:Scheme.{u}} [IsIntegral X] (c:X⟶Spec (.of K))
    [SmoothOfRelativeDimension 1 c] [IsProper c]

/-- The fixed two-stage generic-stalk comparison retains the actual place
of the SAME affine Scheme point. No chosen place/point correspondence is
assumed in this composition. -/
theorem chart_transport_place (j:Spec (.of R)⟶X) [IsOpenImmersion j]
    (hj:j≫c=Spec.map (CommRingCat.ofHom (algebraMap K R))) (f:R→ₐ[K]K)
    (e:F≃ₐ[K]FractionRing R) :
    letI:=SmoothCurveExtension.fieldAlgebra c
    Place.congrEquiv e.toRingEquiv e.commutes
      (pointEquivRationalPlace_of_fieldEquiv c
        (e.trans (AffineGenericStalk.fieldEquiv c j hj)) (chartPoint c j hj f)).val=
      (chartPlace c j hj f).val := by
  letI:=SmoothCurveExtension.fieldAlgebra c
  let p:=chartPoint c j hj f
  let v:=pointEquivRationalPlace c p
  let g:=AffineGenericStalk.fieldEquiv c j hj
  apply Place.ext
  ext z
  change (e.trans g) (e.symm z)∈v.val.toValuationSubring ↔g z∈v.val.toValuationSubring
  simp only [AlgEquiv.trans_apply,AlgEquiv.apply_symm_apply]

/-- Every original affine ring coordinate is regular and has its original
value under the FIXED supplied F->Frac(R)->generic-stalk comparison. -/
theorem chart_transport_evaluate (j:Spec (.of R)⟶X) [IsOpenImmersion j]
    (hj:j≫c=Spec.map (CommRingCat.ofHom (algebraMap K R))) (f:R→ₐ[K]K)
    (e:F≃ₐ[K]FractionRing R) (x:F) (r:R)
    (hex:e x=algebraMap R (FractionRing R) r) :
    letI:=SmoothCurveExtension.fieldAlgebra c
    let v:=pointEquivRationalPlace_of_fieldEquiv c
      (e.trans (AffineGenericStalk.fieldEquiv c j hj)) (chartPoint c j hj f)
    ∃b:v.val.toValuationSubring,(b:F)=x ∧ ResiduePlaceEvaluation.evaluate v.val v.property b=f r := by
  letI:=SmoothCurveExtension.fieldAlgebra c
  let v:=pointEquivRationalPlace_of_fieldEquiv c
      (e.trans (AffineGenericStalk.fieldEquiv c j hj)) (chartPoint c j hj f)
  let w:=chartPlace c j hj f
  have hvw:=chart_transport_place c j hj f e
  have hmem:x∈v.val.toValuationSubring := by
    have hr:=chart_regular c j hj f r
    rw [←hvw] at hr
    change e.symm (algebraMap R (FractionRing R) r)∈v.val.toValuationSubring at hr
    rwa [←hex,AlgEquiv.symm_apply_apply] at hr
  let b:v.val.toValuationSubring:=⟨x,hmem⟩
  let d:w.val.toValuationSubring:=⟨algebraMap R (FractionRing R) r,chart_regular c j hj f r⟩
  have hd:(d:FractionRing R)=e (b:F) := hex.symm
  have he:=evaluate_congr_of_eq e v.val v.property w.val w.property hvw b d hd
  refine ⟨b,rfl,?_⟩
  exact he.symm.trans (chart_evaluate c j hj f r)

#print axioms evaluate_congr_of_eq
#print axioms chart_transport_place
#print axioms chart_transport_evaluate
end FourCorner.FixedAffinePointEvaluation
