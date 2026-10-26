import AllPointStalkUnramified

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.AllPointSchemeProperties
open AllPointStalkUnramified SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces SmoothProperPlaceNaturality

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [Algebra Y.functionField X.functionField]

/-- The actual generic-point stalk map is the actual separable field map,
up to the proved native stalk identifications. -/
theorem generic_stalk_unramified (π : X ⟶ Y)
    (hg : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y))
    (hτ : (algebraMap Y.functionField X.functionField).FormallyUnramified) :
    (π.stalkMap (genericPoint X)).hom.FormallyUnramified := by
  have hy := image_generic π hg
  have hBX : Function.Bijective (stalkEmbedding X (genericPoint X)) :=
    embedding_bijective_at_generic X _ rfl

  have hBA : Function.Bijective (stalkEmbedding Y (π (genericPoint X))) := by
    exact embedding_bijective_at_generic Y _ hy
  let eA := RingEquiv.ofBijective (stalkEmbedding Y (π (genericPoint X))) hBA
  let eB := RingEquiv.ofBijective (stalkEmbedding X (genericPoint X)) hBX
  apply formallyUnramified_of_square (π.stalkMap (genericPoint X)).hom
    (algebraMap Y.functionField X.functionField) eA eB ?_ hτ
  apply RingHom.ext
  intro a
  change stalkEmbedding X (genericPoint X)
    ((π.stalkMap (genericPoint X)).hom a)=
      algebraMap Y.functionField X.functionField (stalkEmbedding Y (π (genericPoint X)) a)
  simpa only [stalkEmbedding,RingHom.algebraMap_toAlgebra] using (stalk_field_naturality π hg (genericPoint X) a).symm

variable (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
  [SmoothOfRelativeDimension 1 cX] [SmoothOfRelativeDimension 1 cY] [IsProper cX] [IsProper cY]

/-- All closed points, of every residue degree, inherit native unramified
stalk maps from the actual valuation-ring restriction maps. -/
theorem closed_stalk_unramified [FiniteDimensional Y.functionField X.functionField]
    (htower : letI := fieldAlgebra cX;letI := fieldAlgebra cY;IsScalarTower K Y.functionField X.functionField)
    (π : X ⟶ Y)
    (hg : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y))
    (hplaces : letI := fieldAlgebra cX;letI := fieldAlgebra cY;letI := htower
      ∀ w : Place K X.functionField,(Place.restrictInclusion Y.functionField w).FormallyUnramified)
    (x : closedPoints X) (hy : IsClosed ({π x.val} : Set Y)) :
    (π.stalkMap x.val).hom.FormallyUnramified := by
  letI := fieldAlgebra cX
  letI := fieldAlgebra cY
  letI := htower
  let w := placeOfClosedPoint cX x
  have hrY := closed_point_comap cX cY htower π hg x hy
  let eA := stalkValuationEquivOfRange Y (π x.val) (w.restrict Y.functionField).toValuationSubring hrY
  let eB := stalkValuationEquiv cX x
  apply formallyUnramified_of_square (π.stalkMap x.val).hom (Place.restrictInclusion Y.functionField w) eA eB ?_ (hplaces w)
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change algebraMap (X.presheaf.stalk x.val) X.functionField ((π.stalkMap x.val).hom a)=
    algebraMap Y.functionField X.functionField (algebraMap (Y.presheaf.stalk (π x.val)) Y.functionField a)
  exact (stalk_field_naturality π hg x.val a).symm

/-- Native all-point stalk unramifiedness: the generic point and every
closed point are both proved, without restricting to rational points. -/
theorem all_stalks_unramified [FiniteDimensional Y.functionField X.functionField]
    (htower : letI := fieldAlgebra cX;letI := fieldAlgebra cY;IsScalarTower K Y.functionField X.functionField)
    (π : X ⟶ Y) (hπ : π ≫ cY=cX)
    (hg : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y))
    (hτ : (algebraMap Y.functionField X.functionField).FormallyUnramified)
    (hplaces : letI := fieldAlgebra cX;letI := fieldAlgebra cY;letI := htower
      ∀ w : Place K X.functionField,(Place.restrictInclusion Y.functionField w).FormallyUnramified) :
    ∀ x : X,(π.stalkMap x).hom.FormallyUnramified := by
  haveI : IsProper (π ≫ cY) := by rw [hπ];infer_instance
  haveI : IsProper π := IsProper.of_comp π cY
  intro x
  by_cases hx : x=genericPoint X
  · subst x
    exact generic_stalk_unramified π hg hτ
  · have hclosed := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint cX x hx
    have hy : IsClosed ({π x} : Set Y) := by simpa only [Set.image_singleton] using π.isClosedMap {x} hclosed
    exact closed_stalk_unramified cX cY htower π hg hplaces ⟨x,hclosed⟩ hy

/-- Actual native finiteness and formal unramifiedness from the proved
native field/stalk/Place data, with no model-identification premise. -/
theorem finite_and_unramified [FiniteDimensional Y.functionField X.functionField]
    (htower : letI := fieldAlgebra cX;letI := fieldAlgebra cY;IsScalarTower K Y.functionField X.functionField)
    (π : X ⟶ Y) (hπ : π ≫ cY=cX)
    (hg : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y))
    (hτ : (algebraMap Y.functionField X.functionField).FormallyUnramified)
    (hplaces : letI := fieldAlgebra cX;letI := fieldAlgebra cY;letI := htower
      ∀ w : Place K X.functionField,(Place.restrictInclusion Y.functionField w).FormallyUnramified) :
    IsFinite π ∧ FormallyUnramified π ∧ LocallyOfFiniteType π := by
  haveI : IsProper (π ≫ cY) := by rw [hπ];infer_instance
  haveI : IsProper π := IsProper.of_comp π cY
  obtain ⟨hfin,hun⟩ := CriticalCoverSchemeProperties.finite_and_formallyUnramified_of_all_stalks π
    (all_stalks_unramified cX cY htower π hπ hg hτ hplaces)
  exact ⟨hfin,hun,inferInstance⟩

#print axioms generic_stalk_unramified
#print axioms closed_stalk_unramified
#print axioms all_stalks_unramified
#print axioms finite_and_unramified
end FourCorner.AllPointSchemeProperties
