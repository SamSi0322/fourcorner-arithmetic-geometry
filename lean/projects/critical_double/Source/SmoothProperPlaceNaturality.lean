import AffineChartStalkFunctions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.SmoothProperPlaceNaturality
open SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces AffineChartStalkFunctions
variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [Algebra Y.functionField X.functionField]

/-- The ACTUAL generic Spec diagram proves actual local-function pullback
inside the given native function-field embedding, at every source point. -/
theorem stalk_field_naturality (π : X ⟶ Y)
    (hgeneric : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y))
    (x : X) (a : Y.presheaf.stalk (π x)) :
    algebraMap Y.functionField X.functionField
      (algebraMap (Y.presheaf.stalk (π x)) Y.functionField a)=
        algebraMap (X.presheaf.stalk x) X.functionField ((π.stalkMap x).hom a) := by
  have heq : CommRingCat.ofHom ((algebraMap Y.functionField X.functionField).comp
      (algebraMap (Y.presheaf.stalk (π x)) Y.functionField))=
      CommRingCat.ofHom ((algebraMap (X.presheaf.stalk x) X.functionField).comp (π.stalkMap x).hom) := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk (π x))).mp
    rw [CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,Spec.map_comp]
    simp only [CommRingCat.ofHom_hom,Category.assoc]
    rw [functionField_stalk_diagram (π x),←hgeneric,
      Scheme.SpecMap_stalkMap_fromSpecStalk,←Category.assoc,functionField_stalk_diagram x]
  exact congrArg (fun f : Y.presheaf.stalk (π x) ⟶ X.presheaf.stalk (genericPoint X) => f.hom a) heq

variable (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
  [SmoothOfRelativeDimension 1 cX] [SmoothOfRelativeDimension 1 cY] [IsProper cX] [IsProper cY]

/-- The actual mapped Scheme K-section, retaining the original morphism. -/
def mappedPoint (π : X ⟶ Y) (hπ : π ≫ cY=cX) (p : RationalPoint cX) : RationalPoint cY :=
  ⟨p.val ≫ π,by rw [Category.assoc,hπ];exact p.property⟩

/-- Generic-diagram naturality forces the target point's actual valuation
ring to be the comap of the same source point's actual valuation ring. The
finite native field extension supplies genuine nontrivial restriction. -/
theorem point_valuation_comap [FiniteDimensional Y.functionField X.functionField]
    (htower : letI := fieldAlgebra cX;letI := fieldAlgebra cY;
      IsScalarTower K Y.functionField X.functionField)
    (π : X ⟶ Y) (hπ : π ≫ cY=cX)
    (hgeneric : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y)) (p : RationalPoint cX) :
    letI := fieldAlgebra cX;letI := fieldAlgebra cY
    ((pointEquivRationalPlace cY (mappedPoint cX cY π hπ p)).val).toValuationSubring=
      ((pointEquivRationalPlace cX p).val).toValuationSubring.comap
        (algebraMap Y.functionField X.functionField) := by
  letI := fieldAlgebra cX
  letI := fieldAlgebra cY
  letI := htower
  let v := pointEquivRationalPlace cX p
  let q := mappedPoint cX cY π hπ p
  let w := pointEquivRationalPlace cY q
  let x := p.val (IsLocalRing.closedPoint K)
  have hX : (algebraMap (X.presheaf.stalk x) X.functionField).range=v.val.toValuationSubring.toSubring :=
    pointEquivRationalPlace_range cX p
  have hY : (algebraMap (Y.presheaf.stalk (π x)) Y.functionField).range=w.val.toValuationSubring.toSubring :=
    pointEquivRationalPlace_range cY q
  have hle : w.val.toValuationSubring≤v.val.toValuationSubring.comap
      (algebraMap Y.functionField X.functionField) := by
    intro r hr
    have hrange : r∈(algebraMap (Y.presheaf.stalk (π x)) Y.functionField).range := by rw [hY];exact hr
    obtain ⟨a,ha⟩ := hrange
    have hxmem : algebraMap (X.presheaf.stalk x) X.functionField ((π.stalkMap x).hom a)∈v.val.toValuationSubring := by
      change _∈v.val.toValuationSubring.toSubring
      rw [←hX]
      exact ⟨_,rfl⟩
    change algebraMap Y.functionField X.functionField r∈v.val.toValuationSubring
    have he : algebraMap Y.functionField X.functionField r=
        algebraMap (X.presheaf.stalk x) X.functionField ((π.stalkMap x).hom a) :=
      (congrArg (algebraMap Y.functionField X.functionField) ha.symm).trans
        (stalk_field_naturality π hgeneric x a)
    exact he.symm ▸ hxmem
  exact ValuationSubring.eq_of_le_of_ne_top w.val.toValuationSubring hle
    (v.val.restrict Y.functionField).ne_top'

/-- The SAME target-point Place is exactly restriction of the SAME
source-point Place along the actual native generic embedding. -/
theorem point_place_restrict [FiniteDimensional Y.functionField X.functionField]
    (htower : letI := fieldAlgebra cX;letI := fieldAlgebra cY;
      IsScalarTower K Y.functionField X.functionField)
    (π : X ⟶ Y) (hπ : π ≫ cY=cX)
    (hgeneric : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y)) (p : RationalPoint cX) :
    letI := fieldAlgebra cX;letI := fieldAlgebra cY;letI := htower
    (pointEquivRationalPlace cX p).val.restrict Y.functionField=
      (pointEquivRationalPlace cY (mappedPoint cX cY π hπ p)).val := by
  letI := fieldAlgebra cX
  letI := fieldAlgebra cY
  letI := htower
  apply Place.ext
  exact (point_valuation_comap cX cY htower π hπ hgeneric p).symm

#print axioms stalk_field_naturality
#print axioms mappedPoint
#print axioms point_valuation_comap
#print axioms point_place_restrict
end FourCorner.SmoothProperPlaceNaturality
