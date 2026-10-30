import ThetaCoverClassPortable.SchemePointStalkEvaluation
import ThetaCoverClassPortable.RationalPlaceEvaluationUnique

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.SmoothProperRationalPointPlaces
open SmoothProperClosedPointPlaces SchemePointStalkEvaluation
open ResiduePlaceEvaluation RationalPlaceEvaluationUnique
variable {K : Type u} [Field K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 c] [IsProper c]

abbrev RationalPoint := {p : Spec (CommRingCat.of K) ⟶ X // p ≫ c=𝟙 _}

/-- Compatibility of the SAME structural field map with every actual stalk. -/
theorem baseToFunctionField_stalk (x : X) (a : K) :
    baseToFunctionField c a=algebraMap (X.presheaf.stalk x) X.functionField (stalkBaseMap c x a) := by
  have key : ∀ s : Γ(X,⊤), (X.presheaf.germ ⊤ (genericPoint X) trivial).hom s=
      algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ ⊤ x trivial).hom s) := by
    intro s
    simp_rw [RingHom.algebraMap_toAlgebra]
    change _=(X.presheaf.germ ⊤ x trivial ≫ X.presheaf.stalkSpecializes _).hom s
    exact congrArg (fun f : Γ(X,⊤) ⟶ X.presheaf.stalk (genericPoint X) => f.hom s)
      (X.presheaf.germ_stalkSpecializes (U:=⊤) (y:=x) trivial (genericPoint_specializes x)) |>.symm
  exact key _

/-- The stalk/valuation identification preserves the original K-structure. -/
def stalkValuationAlgEquiv (x : closedPoints X) :
    letI := fieldAlgebra c
    letI := stalkAlgebra c x.val
    X.presheaf.stalk x.val ≃ₐ[K] (placeOfClosedPoint c x).toValuationSubring := by
  letI := fieldAlgebra c
  letI := stalkAlgebra c x.val
  apply AlgEquiv.ofRingEquiv (f:=stalkValuationEquiv c x)
  intro a
  apply Subtype.ext
  change ((stalkValuationEquiv c x (stalkBaseMap c x.val a) : (placeOfClosedPoint c x).toValuationSubring) : X.functionField)=
    algebraMap K X.functionField a
  rw [stalkValuationEquiv_coe,← baseToFunctionField_stalk c]
  rfl

/-- Every genuine over-K point gives an actual rational place of the SAME
function field. Rationality is derived from its actual stalk evaluation. -/
def pointToRationalPlace (p : RationalPoint c) :
    letI := fieldAlgebra c; {v : Place K X.functionField // v.IsRational} := by
  letI := fieldAlgebra c
  let x := closedPointOfPoint c p.val p.property
  letI := stalkAlgebra c x.val
  letI := stalkAlgebra c (p.val (IsLocalRing.closedPoint K))
  let v := placeOfClosedPoint c x
  let f : v.toValuationSubring →ₐ[K] K :=
    (pointEvaluation c p.val p.property).comp (stalkValuationAlgEquiv c x).symm.toAlgHom
  exact ⟨v,isRational_of_algHom v f⟩

/-- A rational place gives a genuine K-point of the original curve by its
actual centre and the original residue evaluation. -/
def pointOfRationalPlace :
    letI := fieldAlgebra c
    {v : Place K X.functionField // v.IsRational} → RationalPoint c := by
  letI := fieldAlgebra c
  intro v
  let x := (closedPointPlaceEquiv c).symm v.val
  have hx : placeOfClosedPoint c x=v.val := (closedPointPlaceEquiv c).apply_symm_apply v.val
  have hvr : (placeOfClosedPoint c x).IsRational := hx.symm ▸ v.property
  letI := stalkAlgebra c x.val
  let f : X.presheaf.stalk x.val →ₐ[K] K :=
    (evaluate (placeOfClosedPoint c x) hvr).comp (stalkValuationAlgEquiv c x).toAlgHom
  exact ⟨pointOfEvaluation c x.val f,pointOfEvaluation_over c x.val f⟩

theorem pointOfRationalPlace_closedPoint :
    letI := fieldAlgebra c
    ∀ v : {v : Place K X.functionField // v.IsRational},
      (pointOfRationalPlace c v).val (IsLocalRing.closedPoint K)=
        ((closedPointPlaceEquiv c).symm v.val).val := by
  letI := fieldAlgebra c
  intro v
  exact pointOfEvaluation_closedPoint c _ _

theorem pointToRationalPlace_val (p : RationalPoint c) :
    letI := fieldAlgebra c
    (pointToRationalPlace c p).val=placeOfClosedPoint c (closedPointOfPoint c p.val p.property) := rfl

theorem point_left_inverse :
    letI := fieldAlgebra c
    Function.LeftInverse (pointOfRationalPlace c) (pointToRationalPlace c) := by
  letI := fieldAlgebra c
  intro p
  apply Subtype.ext
  apply point_ext c _ _ (pointOfRationalPlace c (pointToRationalPlace c p)).property p.property
  rw [pointOfRationalPlace_closedPoint,pointToRationalPlace_val]
  change ((closedPointPlaceEquiv c).symm ((closedPointPlaceEquiv c)
    (closedPointOfPoint c p.val p.property))).val=p.val (IsLocalRing.closedPoint K)
  rw [Equiv.symm_apply_apply]
  rfl

theorem place_right_inverse :
    letI := fieldAlgebra c
    Function.RightInverse (pointOfRationalPlace c) (pointToRationalPlace c) := by
  letI := fieldAlgebra c
  intro v
  apply Subtype.ext
  rw [pointToRationalPlace_val]
  have hx : closedPointOfPoint c (pointOfRationalPlace c v).val (pointOfRationalPlace c v).property=
      (closedPointPlaceEquiv c).symm v.val := by
    apply Subtype.ext
    exact pointOfRationalPlace_closedPoint c v
  rw [hx]
  exact (closedPointPlaceEquiv c).apply_symm_apply v.val

/-- Genuine K-points of a smooth proper integral relative-dimension-one
curve correspond to rational places of its SAME function field, over any
field K. No algebraic closure or characteristic-zero hypothesis is used. -/
def pointEquivRationalPlace :
    letI := fieldAlgebra c
    RationalPoint c ≃ {v : Place K X.functionField // v.IsRational} := by
  letI := fieldAlgebra c
  exact ⟨pointToRationalPlace c,pointOfRationalPlace c,point_left_inverse c,place_right_inverse c⟩

/-- The equivalence retains the actual stalk subring inside the original
function field; this pins its centre and all regular function coordinates. -/
theorem pointEquivRationalPlace_range (p : RationalPoint c) :
    letI := fieldAlgebra c
    (algebraMap (X.presheaf.stalk (p.val (IsLocalRing.closedPoint K))) X.functionField).range=
      ((pointEquivRationalPlace c p).val).toValuationSubring.toSubring := by
  letI := fieldAlgebra c
  exact range_stalk c (closedPointOfPoint c p.val p.property)

/-- Actual residue evaluation of every actual local function agrees with
the same original Scheme K-point. No unrelated point/field model is used. -/
theorem pointEquivRationalPlace_evaluate (p : RationalPoint c)
    (a : X.presheaf.stalk (p.val (IsLocalRing.closedPoint K))) :
    letI := fieldAlgebra c
    letI := stalkAlgebra c (p.val (IsLocalRing.closedPoint K))
    evaluate (pointEquivRationalPlace c p).val (pointEquivRationalPlace c p).property
      (stalkValuationEquiv c (closedPointOfPoint c p.val p.property) a)=
      pointEvaluation c p.val p.property a := by
  letI := fieldAlgebra c
  letI := stalkAlgebra c (p.val (IsLocalRing.closedPoint K))
  let x := closedPointOfPoint c p.val p.property
  letI := stalkAlgebra c x.val
  let v := placeOfClosedPoint c x
  change ((evaluate v (pointToRationalPlace c p).property).comp
    (stalkValuationAlgEquiv c x).toAlgHom) a=pointEvaluation c p.val p.property a
  exact AlgHom.congr_fun (localEval_unique _ _) a

/-- Exact cardinality transport, including finite constant fields. -/
theorem natCard_points_eq_rationalPlaces :
    letI := fieldAlgebra c
    Nat.card (RationalPoint c)=Nat.card {v : Place K X.functionField // v.IsRational} := by
  letI := fieldAlgebra c
  exact Nat.card_congr (pointEquivRationalPlace c)

#print axioms pointEquivRationalPlace_range
#print axioms pointEquivRationalPlace_evaluate
#print axioms natCard_points_eq_rationalPlaces

#print axioms baseToFunctionField_stalk
#print axioms stalkValuationAlgEquiv
#print axioms pointToRationalPlace
#print axioms pointOfRationalPlace
#print axioms point_left_inverse
#print axioms place_right_inverse
#print axioms pointEquivRationalPlace
end FourCorner.SmoothProperRationalPointPlaces
