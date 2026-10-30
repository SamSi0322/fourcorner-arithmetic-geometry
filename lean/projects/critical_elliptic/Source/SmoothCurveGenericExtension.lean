import SmoothCurveValuation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace FourCorner.SmoothCurveExtension

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

theorem separated_of_over (d : Y ⟶ Spec (CommRingCat.of K))
    [IsSeparated d] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from d]; infer_instance⟩

theorem existence_of_proper {S : Scheme.{u}} (d : Y ⟶ S) [IsProper d] :
    ValuativeCriterion.Existence d := by
  have h : IsProper d := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1.existence

/-- A generic map from an arbitrary-field smooth integral curve extends to a
proper target. No choice of a different curve model is made. -/
theorem extend_generic (c : X ⟶ Spec (CommRingCat.of K))
    (d : Y ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 c] [IsProper d]
    (f : Spec X.functionField ⟶ Y)
    (hf : f ≫ d = X.fromSpecStalk (genericPoint X) ≫ c) :
    ∃ π : X ⟶ Y, π ≫ d = c ∧ X.fromSpecStalk (genericPoint X) ≫ π = f := by
  haveI : Y.IsSeparated := separated_of_over d
  let f₀ : X.PartialMap Y := Scheme.PartialMap.ofFromSpecStalk c d f hf
  have hf₀ : f₀.hom ≫ d = f₀.domain.ι ≫ c :=
    Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _
  have hη : genericPoint X ∈ f₀.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hf₀η : f₀.fromSpecStalkOfMem hη = f :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
  have hdom : f₀.toRationalMap.domain = ⊤ := top_unique fun x _ =>
    mem_domain_of_valuationRing c d (existence_of_proper d) f₀ hf₀ x
      (valuationRing_stalk c x)
  let g := f₀.toRationalMap.toPartialMap
  let π : X ⟶ Y := X.topIso.inv ≫ X.homOfLE hdom.ge ≫ g.hom
  have hι : f₀.domain.ι ≫ π = f₀.hom := by
    have key := f₀.toPartialMap_toRationalMap_restrict
    change X.homOfLE f₀.le_domain_toRationalMap ≫ g.hom = f₀.hom at key
    have hcomp : (f₀.domain.ι ≫ X.topIso.inv) ≫ X.homOfLE hdom.ge =
        X.homOfLE f₀.le_domain_toRationalMap := by
      apply (cancel_mono (Scheme.Opens.ι f₀.toRationalMap.domain)).mp
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.toIso_inv_ι, Category.comp_id]
    calc
      f₀.domain.ι ≫ π = ((f₀.domain.ι ≫ X.topIso.inv) ≫ X.homOfLE hdom.ge) ≫ g.hom := by
        dsimp only [π]
        simp only [Category.assoc]
      _ = f₀.hom := by rw [hcomp]; exact key
  refine ⟨π, ?_, ?_⟩
  · haveI : IsDominant f₀.domain.ι :=
      ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact f₀.dense_domain⟩
    refine ext_of_isDominant f₀.domain.ι ?_
    rw [reassoc_of% hι, hf₀]
  · rw [← Scheme.Opens.fromSpecStalkOfMem_ι f₀.domain (genericPoint X) hη,
      Category.assoc, hι]
    exact hf₀η

theorem generic_dominant (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  refine ⟨?_⟩
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk (genericPoint X)) :=
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  have hd : Dense ({genericPoint X} : Set X) :=
    dense_iff_closure_eq.mpr (genericPoint_spec X).def
  exact hd.mono (Set.singleton_subset_iff.mpr hη)

theorem hom_ext_generic (d : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated d] {f g : X ⟶ Y}
    (h : X.fromSpecStalk (genericPoint X) ≫ f =
      X.fromSpecStalk (genericPoint X) ≫ g) : f = g := by
  haveI : Y.IsSeparated := separated_of_over d
  haveI := generic_dominant X
  exact ext_of_isDominant (X.fromSpecStalk (genericPoint X)) h

end FourCorner.SmoothCurveExtension
#print axioms FourCorner.SmoothCurveExtension.extend_generic
#print axioms FourCorner.SmoothCurveExtension.hom_ext_generic
