import ThetaCoverClassPortable.SplitAlgebraCoordinates
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardChartSections
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open scoped TensorProduct
namespace FourCorner.SplitCurveSections
open AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
variable (F : Type u) [CommRing F] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of F))
  (B : Type u) [CommRing B] [Algebra F B]
  (ι : Spec (CommRingCat.of B) ⟶ C)
  (hι : ι ≫ c = specMap F B)
  (R : Type u) [CommRing R] [Algebra F R]
  (m : ℕ) (φ : (R ⊗[F] B) ≃ₐ[R] (Fin m → R))

noncomputable def curvePoint (j : Fin m) : Spec (CommRingCat.of R) ⟶ C :=
  Spec.map (CommRingCat.ofHom (SplitAlgebraCoordinates.coordinate F R B m φ j).toRingHom) ≫ ι

lemma curvePoint_over (hι : ι ≫ c = specMap F B) (j : Fin m) : curvePoint F B ι R m φ j ≫ c = specMap F R := by
  rw [curvePoint, Category.assoc, hι, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (SplitAlgebraCoordinates.coordinate F R B m φ j).comp_algebraMap

noncomputable def splitSection (hι : ι ≫ c = specMap F B) (j : Fin m) : SchemeHomOver (𝟙 _) (baseChange F c R) :=
  ⟨pullback.lift (curvePoint F B ι R m φ j) (𝟙 _) (by
      rw [curvePoint_over (F := F) (c := c) (B := B) (ι := ι) (R := R) (m := m) (φ := φ) hι, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

@[reassoc] lemma section_fst (j : Fin m) :
    (splitSection (F := F) (c := c) (B := B) (ι := ι) (R := R) (m := m) (φ := φ) hι j).1 ≫ pullback.fst c (specMap F R) = curvePoint F B ι R m φ j :=
  pullback.lift_fst _ _ _

/-- The actual curve sections are distinct after ANY field-valued base map. -/
theorem section_geometric_injective [Mono ι]
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (fun j => s ≫ (splitSection (F := F) (c := c) (B := B) (ι := ι) (R := R) (m := m) (φ := φ) hι j).1) := by
  intro j j' h
  have hC := congrArg (fun q => q ≫ pullback.fst c (specMap F R)) h
  simp only [Category.assoc, section_fst] at hC
  have hB : s ≫ Spec.map (CommRingCat.ofHom (SplitAlgebraCoordinates.coordinate F R B m φ j).toRingHom) =
      s ≫ Spec.map (CommRingCat.ofHom (SplitAlgebraCoordinates.coordinate F R B m φ j').toRingHom) := by
    apply (cancel_mono ι).mp
    simpa only [Category.assoc, curvePoint] using hC
  obtain ⟨τ, rfl⟩ := Spec.map_surjective s
  rw [← Spec.map_comp, ← Spec.map_comp] at hB
  have hring := congrArg CommRingCat.Hom.hom (Spec.map_injective hB)
  exact SplitAlgebraCoordinates.coordinate_injective_after_field F R B m φ k τ.hom hring

theorem sectionFibrePoint_injective [Mono ι]
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (fun j => AlgebraicGeometry.RelPicard.sectionFibrePoint
      (splitSection (F := F) (c := c) (B := B) (ι := ι) (R := R) (m := m) (φ := φ) hι j) s) := by
  intro j j' h
  apply section_geometric_injective F c B ι hι R m φ k s
  have ht := congrArg (fun q => q.1 ≫ pullback.fst (baseChange F c R) s) h
  simpa only [AlgebraicGeometry.RelPicard.sectionFibrePoint, pullback.lift_fst] using ht

end FourCorner.SplitCurveSections
