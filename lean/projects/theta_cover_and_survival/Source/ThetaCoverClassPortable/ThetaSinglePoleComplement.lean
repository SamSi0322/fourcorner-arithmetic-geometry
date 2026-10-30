import ThetaCoverClassPortable.IsoNativeStalkRange
import ThetaCoverClassPortable.SinglePoleChartAlgebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels CurveModel NativeSinglePoleCharts
attribute [local instance] sourceIntegral sourceSmooth sourceProper constants

variable (f : (C ℚ).functionField) [Fact (f≠0)]
  [FiniteDimensional ℚ⟮f⟯ (C ℚ).functionField]
  [FiniteDimensional ℚ⟮f⁻¹⟯ (C ℚ).functionField]
  (ht : Transcendental ℚ f) (i : C ℚ ≅ glued ℚ f)
  (hg : (C ℚ).fromSpecStalk (genericPoint (C ℚ)) ≫ i.hom =
    Spec.map (CommRingCat.ofHom (gluedFunctionFieldEquiv ℚ f).symm.toRingHom) ≫
      (glued ℚ f).fromSpecStalk (genericPoint (glued ℚ f)))

private theorem image_closed (x : C ℚ) (hx : IsClosed ({x} : Set (C ℚ))) :
    IsClosed ({i.hom x} : Set (glued ℚ f)) := by
  have h := i.hom.homeomorph.isClosedMap _ hx
  simpa only [Set.image_singleton, Scheme.Hom.homeomorph_apply] using h

include hg in
private theorem model_place_stalk_range (x : C ℚ) (hx : IsClosed ({x} : Set (C ℚ))) :
    (algebraMap ((C ℚ).presheaf.stalk x) (C ℚ).functionField).range =
      (gluedPlaceOfPoint ℚ f ht ⟨i.hom x,image_closed f i x hx⟩).toValuationSubring.toSubring := by
  rw [← NativeSinglePoleCharts.iso_stalk_range i (gluedFunctionFieldEquiv ℚ f).symm hg x]
  exact range_stalk_eq_gluedPlaceOfPoint ℚ f ht ⟨i.hom x,image_closed f i x hx⟩

private theorem mem_chart_iff_place_mem (y : closedPoints (glued ℚ f)) :
    y.val ∈ Set.range (ι₀ ℚ f).base ↔
      f ∈ (gluedPlaceOfPoint ℚ f ht y).toValuationSubring := by
  constructor
  · rintro ⟨p,hp⟩
    have hy : y=⟨ι₀ ℚ f p,by rw [hp]; exact y.property⟩ := Subtype.ext hp.symm
    rw [hy,gluedPlaceOfPoint_ι₀]
    exact t_mem_of_ι₀ ℚ f ht p _
  · intro hf
    by_contra hy
    obtain ⟨p,hp⟩ := mem_range_ιInf_of_not_mem_range_ι₀ ℚ f hy
    rw [gluedPlaceOfPoint_of_not_mem ℚ f ht y hy p hp] at hf
    exact t_not_mem_of_ιInf ℚ f ht p _ (tInvChart_mem_of_not_mem_range ℚ f p (hp ▸ hy)) hf

private theorem place_mem_iff_nonneg (v : Place ℚ (C ℚ).functionField) :
    f ∈ v.toValuationSubring ↔ 0≤v.ord f := by
  constructor
  · intro hf
    obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨n,u,hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x:=(⟨f,hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using (Fact.out : f≠0)) hπ
    have hcoe : f=((u:v.toValuationSubring) : (C ℚ).functionField)*((π:(C ℚ).functionField)^(n:ℤ)) := by
      have h := congrArg Subtype.val hu
      push_cast at h
      rw [zpow_natCast]
      exact h
    rw [hcoe,v.ord_unit_smul_zpow u hπ (n:ℤ)]
    exact Int.natCast_nonneg n
  · intro hf
    obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u,hu⟩ := v.exists_unit_mul_zpow (Fact.out : f≠0) hπ
    rw [hu,show v.ord f=(((v.ord f).toNat:ℕ):ℤ) from (Int.toNat_of_nonneg hf).symm,zpow_natCast]
    exact mul_mem (u:v.toValuationSubring).2 (pow_mem (π:v.toValuationSubring).2 _)

include hg ht in
theorem closedPoint_mem_U_iff (r : ℕ) (hr : 0<r) (hpole : originPlace.ord f=-(r:ℤ))
    (haway : ∀ v : Place ℚ (C ℚ).functionField, v≠originPlace → 0≤v.ord f)
    (x : C ℚ) (hx : IsClosed ({x} : Set (C ℚ))) :
    x ∈ NativeSinglePoleCharts.U f i ↔ x≠OC.1 (IsLocalRing.closedPoint ℚ) := by
  let v := gluedPlaceOfPoint ℚ f ht ⟨i.hom x,image_closed f i x hx⟩
  have hv : v=originPlace ↔ x=OC.1 (IsLocalRing.closedPoint ℚ) := by
    constructor
    · intro hv
      apply eq_of_range_stalk_eq (cToBase ℚ)
      exact (model_place_stalk_range f ht i hg x hx).trans
        ((congrArg (fun w : Place ℚ (C ℚ).functionField => w.toValuationSubring.toSubring) hv).trans
          originPlace_stalk_range.symm)
    · intro h
      apply Place.ext
      apply ValuationSubring.toSubring_injective
      rw [← model_place_stalk_range f ht i hg x hx,h,originPlace_stalk_range]
  have hmem : x ∈ NativeSinglePoleCharts.U f i ↔ i.hom x ∈ Set.range (ι₀ ℚ f).base := by
    constructor
    · rintro ⟨p,_,hp⟩
      refine ⟨p,?_⟩
      change i.inv (ι₀ ℚ f p)=x at hp
      rw [←hp]
      exact (congrArg (fun g : glued ℚ f ⟶ glued ℚ f => g (ι₀ ℚ f p)) i.inv_hom_id).symm
    · rintro ⟨p,hp⟩
      exact ⟨p,trivial,by change i.inv (ι₀ ℚ f p)=x; rw [hp]; exact congrArg (fun g : C ℚ ⟶ C ℚ => g x) i.hom_inv_id⟩
  have hmem' : x ∈ NativeSinglePoleCharts.U f i ↔ 0≤v.ord f :=
    hmem.trans ((mem_chart_iff_place_mem f ht ⟨i.hom x,image_closed f i x hx⟩).trans
      (place_mem_iff_nonneg f v))
  rw [hmem']
  constructor
  · intro hn he
    have hv' := hv.mpr he
    rw [hv',hpole] at hn
    omega
  · intro hne
    exact haway v (fun he => hne (hv.mp he))

theorem origin_range_singleton : Set.range OC.1 = {OC.1 (IsLocalRing.closedPoint ℚ)} := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact Set.mem_singleton_iff.mpr (congrArg OC.1 (Subsingleton.elim _ _))
  · intro hx
    exact ⟨IsLocalRing.closedPoint ℚ, (Set.mem_singleton_iff.mp hx).symm⟩

theorem actual_origin_closed : IsClosed ({OC.1 (IsLocalRing.closedPoint ℚ)} : Set (C ℚ)) := by
  letI := origin_closedImmersion
  rw [← origin_range_singleton]
  exact OC.1.isClosedEmbedding.isClosed_range

include hg ht in
theorem singlePole_U_eq_originComplement (r : ℕ) (hr : 0<r) (hpole : originPlace.ord f=-(r:ℤ))
    (haway : ∀ v : Place ℚ (C ℚ).functionField, v≠originPlace → 0≤v.ord f) :
    NativeSinglePoleCharts.U f i=originComplement := by
  have hO : OC.1 (IsLocalRing.closedPoint ℚ) ∉ NativeSinglePoleCharts.U f i := by
    intro h
    exact (closedPoint_mem_U_iff f ht i hg r hr hpole haway _ actual_origin_closed).mp h rfl
  ext x
  have hor : x∈originComplement ↔ x≠OC.1 (IsLocalRing.closedPoint ℚ) := by
    rw [mem_originComplement,origin_range_singleton,Set.mem_singleton_iff]
  change x∈NativeSinglePoleCharts.U f i ↔ x∈originComplement
  rw [hor]
  by_cases hx : x=genericPoint (C ℚ)
  · subst x
    have hu := NativeSinglePoleCharts.generic_mem_U f i
    exact ⟨fun _ he => hO (he ▸ hu), fun _ => hu⟩
  · exact closedPoint_mem_U_iff f ht i hg r hr hpole haway x
      (isClosed_singleton_of_ne_genericPoint (cToBase ℚ) x hx)

end FourCorner.ThetaRationalPicardInput
