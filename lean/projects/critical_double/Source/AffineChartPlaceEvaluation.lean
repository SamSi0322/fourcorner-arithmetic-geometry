import AffineChartStalkFunctions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.AffineChartPlaceEvaluation
open SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces SmoothProperPointPlaceTransport
open SchemePointStalkEvaluation AffineChartStalkFunctions ResiduePlaceEvaluation RationalPlaceEvaluationUnique

section Transport
variable {K F G : Type u} [Field K] [Field F] [Field G] [Algebra K F] [Algebra K G]

def placeValuationAlgEquiv (e : F ≃ₐ[K] G) (v : Place K F) :
    v.toValuationSubring ≃ₐ[K] (Place.congrEquiv e.toRingEquiv e.commutes v).toValuationSubring := by
  let q : v.toValuationSubring ≃+* (Place.congrEquiv e.toRingEquiv e.commutes v).toValuationSubring :=
    Place.comapSymmRingEquiv e.toRingEquiv v.toValuationSubring
  apply AlgEquiv.ofRingEquiv (f:=q)
  intro a
  apply Subtype.ext
  exact e.commutes a

theorem evaluate_congr (e : F ≃ₐ[K] G) (v : Place K F) (hv : v.IsRational)
    (hw : (Place.congrEquiv e.toRingEquiv e.commutes v).IsRational) (b : v.toValuationSubring) :
    evaluate (Place.congrEquiv e.toRingEquiv e.commutes v) hw (placeValuationAlgEquiv e v b)=
      evaluate v hv b := by
  have hh := algHom_unique v ((evaluate _ hw).comp (placeValuationAlgEquiv e v).toAlgHom) (evaluate v hv)
  exact AlgHom.congr_fun hh b
end Transport

variable {K R : Type u} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (CommRingCat.of K))
  [SmoothOfRelativeDimension 1 c] [IsProper c]

/-- The original Scheme point induced by the supplied affine K-evaluation. -/
def chartPoint (j : Spec (CommRingCat.of R) ⟶ X)
    (hj : j ≫ c=Spec.map (CommRingCat.ofHom (algebraMap K R))) (f : R →ₐ[K] K) : RationalPoint c := by
  refine ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j,?_⟩
  rw [Category.assoc,hj,←Spec.map_comp,←CommRingCat.ofHom_comp]
  have he : f.toRingHom.comp (algebraMap K R)=RingHom.id K := by ext a;exact f.commutes a
  rw [he,CommRingCat.ofHom_id,Spec.map_id]

/-- The rational place obtained using the GIVEN native chart fraction-field
comparison, not an arbitrarily chosen field or projective model. -/
def chartPlace (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ c=Spec.map (CommRingCat.ofHom (algebraMap K R))) (f : R →ₐ[K] K) :
    {w : Place K (FractionRing R) // w.IsRational} :=
  pointEquivRationalPlace_of_fieldEquiv c (AffineGenericStalk.fieldEquiv c j hj) (chartPoint c j hj f)

/-- Every original affine ring coordinate is genuinely regular at the
transported actual rational place. -/
theorem chart_regular (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ c=Spec.map (CommRingCat.ofHom (algebraMap K R))) (f : R →ₐ[K] K) (r : R) :
    algebraMap R (FractionRing R) r∈(chartPlace c j hj f).val.toValuationSubring := by
  letI := fieldAlgebra c
  let p := chartPoint c j hj f
  let v := pointEquivRationalPlace c p
  let e := AffineGenericStalk.fieldEquiv c j hj
  change e (algebraMap R (FractionRing R) r)∈v.val.toValuationSubring
  rw [fieldEquiv_chartLocalFunction c j hj f r]
  exact (stalkValuationEquiv c (closedPointOfPoint c p.val p.property) (chartLocalFunction j f r)).property

/-- The residue of every original affine coordinate equals its supplied
K-algebra value at the SAME Scheme point. -/
theorem chart_evaluate (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ c=Spec.map (CommRingCat.ofHom (algebraMap K R))) (f : R →ₐ[K] K) (r : R) :
    evaluate (chartPlace c j hj f).val (chartPlace c j hj f).property
      ⟨algebraMap R (FractionRing R) r,chart_regular c j hj f r⟩=f r := by
  letI := fieldAlgebra c
  let p := chartPoint c j hj f
  let v := pointEquivRationalPlace c p
  let e := AffineGenericStalk.fieldEquiv c j hj
  let x := closedPointOfPoint c p.val p.property
  letI := stalkAlgebra c x.val
  letI := stalkAlgebra c (p.val (IsLocalRing.closedPoint K))
  let b : v.val.toValuationSubring := stalkValuationEquiv c x (chartLocalFunction j f r)
  let bt : (chartPlace c j hj f).val.toValuationSubring := placeValuationAlgEquiv e.symm v.val b
  have hbt : (bt : FractionRing R)=algebraMap R (FractionRing R) r := by
    change e.symm (algebraMap (X.presheaf.stalk (p.val (IsLocalRing.closedPoint K))) X.functionField
      (chartLocalFunction j f r))=_
    have he := fieldEquiv_chartLocalFunction c j hj f r
    exact (congrArg e.symm he.symm).trans (e.symm_apply_apply _)
  have hbeq : bt=⟨algebraMap R (FractionRing R) r,chart_regular c j hj f r⟩ := Subtype.ext hbt
  rw [← hbeq]
  calc
    _=evaluate v.val v.property b := evaluate_congr e.symm v.val v.property (chartPlace c j hj f).property b
    _=pointEvaluation c p.val p.property (chartLocalFunction j f r) :=
      pointEquivRationalPlace_evaluate c p (chartLocalFunction j f r)
    _=f r := chartLocalFunction_evaluate j f r

/-- The exact boundary conversion: affine vanishing is positive valuation
of the SAME nonzero original ring function in the actual rational place. -/
theorem chart_zero_iff_ord_pos (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ c=Spec.map (CommRingCat.ofHom (algebraMap K R))) (f : R →ₐ[K] K)
    (r : R) (hr : r ≠ 0) :
    f r=0 ↔ 0<(chartPlace c j hj f).val.ord (algebraMap R (FractionRing R) r) := by
  have hn : algebraMap R (FractionRing R) r ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne hr
  rw [← chart_evaluate c j hj f r,evaluate_zero_iff_maximal]
  exact (chartPlace c j hj f).val.mem_maximalIdeal_iff_ord_pos hn (chart_regular c j hj f r)

#print axioms placeValuationAlgEquiv
#print axioms evaluate_congr
#print axioms chartPoint
#print axioms chartPlace
#print axioms chart_regular
#print axioms chart_evaluate
#print axioms chart_zero_iff_ord_pos
end FourCorner.AffineChartPlaceEvaluation
