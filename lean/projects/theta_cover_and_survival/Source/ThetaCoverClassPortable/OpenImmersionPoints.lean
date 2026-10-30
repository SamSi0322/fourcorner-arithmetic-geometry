import ThetaCoverClassPortable.PointSupportContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (K : Type) [Field K] [Algebra ℚ K] [TopologicalSpace K]
variable {X Y : Over base} (f : X ⟶ Y) [IsOpenImmersion f.left]

theorem point_range_eq_singleton (P : KPoints K X) :
    Set.range P.left = {pointSupport K P} := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    exact congrArg P.left (Subsingleton.elim (α:=PrimeSpectrum K) t (IsLocalRing.closedPoint K))
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint K,rfl⟩

/-- Actual scheme-theoretic lifting into an open immersion, from the image of Spec K. -/
def openPointLift (P : KPoints K Y) (h : pointSupport K P ∈ Set.range f.left) : KPoints K X :=
  let hr : Set.range P.left ⊆ Set.range f.left := by
    rw [point_range_eq_singleton K P]
    exact Set.singleton_subset_iff.mpr h
  Over.homMk (IsOpenImmersion.lift f.left P.left hr) (by
    rw [←f.w,←Category.assoc,IsOpenImmersion.lift_fac]
    exact P.w)

@[simp] theorem openPointLift_comp (P : KPoints K Y)
    (h : pointSupport K P ∈ Set.range f.left) : openPointLift K f P h ≫ f=P := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem pointMap_injective : Function.Injective (fun P : KPoints K X => P ≫ f) := by
  intro P Q h
  apply Over.OverMorphism.ext
  exact (cancel_mono f.left).mp (congrArg (fun g : pointObject K ⟶ Y => g.left) h)

theorem pointMap_range :
    Set.range (fun P : KPoints K X => P ≫ f) =
      (pointSupport K (X:=Y)) ⁻¹' Set.range f.left := by
  ext P
  constructor
  · rintro ⟨Q,rfl⟩
    exact ⟨pointSupport K Q,rfl⟩
  · intro h
    exact ⟨openPointLift K f P h,openPointLift_comp K f P h⟩

theorem pointMap_isOpen_range [T1Space K] :
    IsOpen (Set.range (fun P : KPoints K X => P ≫ f)) := by
  rw [pointMap_range K f]
  exact f.left.isOpenEmbedding.isOpen_range.preimage (continuous_pointSupport K Y)

/-- Restrict an actual affine test morphism to a principal open lying in an open immersion. -/
def principalChartLift (A : Type) [CommRing A] [Algebra ℚ A]
    (j : pointObject A ⟶ Y) (a : A)
    (h : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆ j.left ⁻¹' Set.range f.left) :
    pointObject (Localization.Away a) ⟶ X :=
  let l : pointObject (Localization.Away a) ⟶ Y :=
    pointChange (Algebra.algHom ℚ A (Localization.Away a)) ≫ j
  let hr : Set.range l.left ⊆ Set.range f.left := by
    rintro _ ⟨x,rfl⟩
    apply h
    apply (PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).le
    exact ⟨x,rfl⟩
  Over.homMk (IsOpenImmersion.lift f.left l.left hr) (by
    rw [←f.w,←Category.assoc,IsOpenImmersion.lift_fac]
    exact l.w)

@[simp] theorem principalChartLift_comp (A : Type) [CommRing A] [Algebra ℚ A]
    (j : pointObject A ⟶ Y) (a : A)
    (h : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆ j.left ⁻¹' Set.range f.left) :
    principalChartLift f A j a h ≫ f =
      pointChange (Algebra.algHom ℚ A (Localization.Away a)) ≫ j := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem principalChart_point_comp (A : Type) [CommRing A] [Algebra ℚ A]
    (j : pointObject A ⟶ Y) (a : A)
    (h : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆ j.left ⁻¹' Set.range f.left)
    (p : {q : A →ₐ[ℚ] K // q a ≠ 0}) :
    affineTest K (CommAlgCat.of ℚ (Localization.Away a)) (principalChartLift f A j a h)
      (localizationPointLift ℚ A K a (Localization.Away a) p) ≫ f =
        affineTest K (CommAlgCat.of ℚ A) j p.1 := by
  unfold affineTest
  rw [Category.assoc,principalChartLift_comp,←Category.assoc,pointChange_comp]
  congr 2
  ext x
  exact localizationPointLift_algebraMap ℚ A K a (Localization.Away a) p x

variable [IsTopologicalDivisionRing K] [T1Space K]

/-- Every actual scheme open immersion is an open map on strong-topology K-points. -/
theorem isOpenMap_pointMap : IsOpenMap (fun P : KPoints K X => P ≫ f) := by
  intro U hU
  change IsOpen[⨆ (A : CommAlgCat ℚ) (j : pointObject A ⟶ Y),
    TopologicalSpace.coinduced (affineTest K A j) inferInstance] _
  simp only [isOpen_iSup_iff,isOpen_coinduced]
  intro A j
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨Q,hQU,hQ⟩ := hp
  have hpW : pointSupport K (pointChange p) ∈ j.left ⁻¹' Set.range f.left := by
    have hh := congrArg (pointSupport K) hQ
    change f.left (pointSupport K Q) = j.left (pointSupport K (pointChange p)) at hh
    exact ⟨pointSupport K Q,hh⟩
  have hW : IsOpen (j.left ⁻¹' Set.range f.left) :=
    f.left.isOpenEmbedding.isOpen_range.preimage j.left.continuous
  obtain ⟨D,⟨a,rfl⟩,hpa,ha⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hW _ hpW
  have hpane : p a ≠ 0 := (affinePointSupport_mem_basicOpen K A p a).mp hpa
  let ψ : {q : A →ₐ[ℚ] K // q a ≠ 0} → KPoints K X := fun q =>
    affineTest K (CommAlgCat.of ℚ (Localization.Away a)) (principalChartLift f A j a ha)
      (localizationPointLift ℚ A K a (Localization.Away a) q)
  have hψ : Continuous ψ :=
    (continuous_affineTest K _ _).comp (continuous_localizationPointLift ℚ A K a _)
  have hψp : ψ ⟨p,hpane⟩=Q := by
    apply pointMap_injective K f
    exact (principalChart_point_comp K f A j a ha ⟨p,hpane⟩).trans hQ.symm
  let N := Subtype.val '' (ψ ⁻¹' U)
  have hNopen : IsOpen N :=
    (isOpen_principalPointSet ℚ A K a).isOpenMap_subtype_val _ (hU.preimage hψ)
  have hpN : p∈N := by
    refine ⟨⟨p,hpane⟩,?_,rfl⟩
    change ψ ⟨p,hpane⟩ ∈ U
    rw [hψp]
    exact hQU
  apply Filter.mem_of_superset (hNopen.mem_nhds hpN)
  rintro q ⟨q',hq',rfl⟩
  exact ⟨ψ q',hq',principalChart_point_comp K f A j a ha q'⟩

/-- Open affine charts are actual open embeddings for the canonical strong topology. -/
theorem isOpenEmbedding_pointMap :
    Topology.IsOpenEmbedding (fun P : KPoints K X => P ≫ f) :=
  .of_continuous_injective_isOpenMap (continuous_pointMap K f)
    (pointMap_injective K f) (isOpenMap_pointMap K f)

end FourCorner.ThetaLocalSurvival.StrongTopology
