import ProperCurveExtension

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.ProperCurveFieldIsoQ
universe u
variable {X Y : Scheme.{0}}

lemma separated_of_proper (c : X ⟶ Spec (.of ℚ)) [IsProper c] : X.IsSeparated := by
  constructor
  rw [← CategoryTheory.Limits.terminal.comp_from c]
  infer_instance

lemma generic_dominant [IsIntegral X] : IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  intro x
  have hr : ({genericPoint X} : Set X) ⊆ Set.range (X.fromSpecStalk (genericPoint X)) := by
    apply Set.singleton_subset_iff.mpr
    exact ⟨IsLocalRing.closedPoint X.functionField,Scheme.fromSpecStalk_closedPoint⟩
  have hc : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hmono := closure_mono hr
  rw [hc] at hmono
  exact hmono trivial

variable (cX : X ⟶ Spec (.of ℚ)) (cY : Y ⟶ Spec (.of ℚ))
    [IsIntegral X] [IsIntegral Y] [IsProper cX] [IsProper cY]
    [SmoothOfRelativeDimension 1 cX] [SmoothOfRelativeDimension 1 cY]
variable (e : X.functionField ≃+* Y.functionField)


def genericForward : Spec (.of X.functionField) ⟶ Y :=
  Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)
def genericBackward : Spec (.of Y.functionField) ⟶ X :=
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X)

lemma genericForward_over : genericForward e ≫ cY = X.fromSpecStalk (genericPoint X) ≫ cX := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _
lemma genericBackward_over : genericBackward e ≫ cX = Y.fromSpecStalk (genericPoint Y) ≫ cY := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

def forward : X ⟶ Y := by
  letI := separated_of_proper cY
  exact ProperCurveExtension.extension cX cY (genericForward e) (genericForward_over cX cY e)
def backward : Y ⟶ X := by
  letI := separated_of_proper cX
  exact ProperCurveExtension.extension cY cX (genericBackward e) (genericBackward_over cX cY e)

lemma generic_forward : X.fromSpecStalk (genericPoint X) ≫ forward cX cY e = genericForward e :=
by
  letI := separated_of_proper cY
  exact ProperCurveExtension.generic_extension cX cY _ _
lemma generic_backward : Y.fromSpecStalk (genericPoint Y) ≫ backward cX cY e = genericBackward e :=
by
  letI := separated_of_proper cX
  exact ProperCurveExtension.generic_extension cY cX _ _

lemma forward_backward : forward cX cY e ≫ backward cX cY e = 𝟙 X := by
  letI := separated_of_proper cX
  haveI := generic_dominant (X := X)
  apply ext_of_isDominant (X.fromSpecStalk (genericPoint X))
  rw [← Category.assoc,generic_forward]
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y) ≫ backward cX cY e = _
  rw [generic_backward]
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X)) = _
  rw [← Category.assoc,← Spec.map_comp]
  have he : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact e.symm_apply_apply a
  rw [he]
  simp

lemma backward_forward : backward cX cY e ≫ forward cX cY e = 𝟙 Y := by
  letI := separated_of_proper cY
  haveI := generic_dominant (X := Y)
  apply ext_of_isDominant (Y.fromSpecStalk (genericPoint Y))
  rw [← Category.assoc,generic_backward]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X) ≫ forward cX cY e = _
  rw [generic_forward]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)) = _
  rw [← Category.assoc,← Spec.map_comp]
  have he : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom e.toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact e.apply_symm_apply a
  rw [he]
  simp

/-- Actual uniqueness isomorphism of smooth proper rational curves from their supplied field equivalence.
The scheme maps are constructed by the proved proper-curve extension argument. -/
def iso : X ≅ Y := ⟨forward cX cY e,backward cX cY e,forward_backward cX cY e,backward_forward cX cY e⟩

end FourCorner.ProperCurveFieldIsoQ
#print axioms FourCorner.ProperCurveFieldIsoQ.iso
