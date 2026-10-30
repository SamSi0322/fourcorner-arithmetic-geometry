import ThetaCoverClassPortable.ThetaDeckInvolution
import ThetaCoverClassPortable.ThetaPairInvariantEquiv
import ThetaCoverClassPortable.ThetaPairGalois
noncomputable section
namespace FourCorner.ThetaActualQuotient
open Algebra AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open ThetaQuotientCharts ThetaChartAlgebras
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev data (j : Fin 3) := ThetaSourcePairData.data j
abbrev ell (j : Fin 3) := algebraMap ℚ (R j) (lambda j)
abbrev hnorm (j : Fin 3) : (data j).a+ell j*(data j).b=1 := base_unit_ideal j
abbrev htwo (j : Fin 3) : IsUnit (2:R j) := ThetaChartFiniteEtale.two_unit (R j)
abbrev fixedAlgebra (j : Fin 3) := ThetaPairInvariantEquiv.fixed (data j)
/-- The literal target chart IS the invariant algebra of the actual normalized involution. -/
def invariantIso (j : Fin 3) : R j ≃ₐ[R j] fixedAlgebra j :=
  ThetaPairInvariantEquiv.equiv (data j) (ell j) (hnorm j) (htwo j)
lemma invariantIso_map (j : Fin 3) (r : R j) : ((invariantIso j r : fixedAlgebra j):S j)=baseMap j r := rfl
/-- Universal invariant-algebra property on every literal target chart, for arbitrary rings. -/
theorem invariant_universal (j : Fin 3) {T : Type} [CommRing T] (f : T →+* S j)
    (hf : (ThetaInvolutionChart.nn j).toRingHom.comp f=f) :
    ∃! g : T →+* R j,(baseMap j).toRingHom.comp g=f :=
  ThetaPairInvariantEquiv.universal (data j) (ell j) (hnorm j) (htwo j) f hf

def kernelPairRingIso (j : Fin 3) : S j ⊗[R j] S j ≃ₐ[R j] S j×S j :=
  ThetaPairGalois.equiv (data j) (ell j) (hnorm j) (htwo j)
lemma kernelPair_formula (j : Fin 3) (s t : S j) :
    kernelPairRingIso j (s ⊗ₜ[R j] t)=(s*t,s*ThetaInvolutionChart.nn j t) :=
  ThetaPairGalois.phi_tmul (data j) s t
abbrev localProjection (j : Fin 3) := Spec.map (CommRingCat.ofHom (baseMap j).toRingHom)
/-- The actual categorical kernel pair on each quotient chart is two copies of
its actual source chart. This retains the original coordinate-algebra base map. -/
def kernelPairSchemeIso (j : Fin 3) :
    Spec (.of (S j)) ⨿ Spec (.of (S j)) ≅ pullback (localProjection j) (localProjection j) :=
  asIso (coprodSpec (S j) (S j)) ≪≫
    Scheme.Spec.mapIso ((kernelPairRingIso j).toRingEquiv.toCommRingCatIso.op) ≪≫
      (pullbackSpecIso (R j) (S j) (S j)).symm
lemma kernelPairSchemeIso_hom (j : Fin 3) :
    (kernelPairSchemeIso j).hom=coprodSpec (S j) (S j) ≫
      Spec.map (CommRingCat.ofHom (kernelPairRingIso j).toRingHom) ≫
        (pullbackSpecIso (R j) (S j) (S j)).inv := rfl

lemma identity_graph_fst (j : Fin 3) :
    coprod.inl ≫ (kernelPairSchemeIso j).hom ≫ pullback.fst (localProjection j) (localProjection j)=𝟙 _ := by
  have hp : (pullbackSpecIso (R j) (S j) (S j)).inv ≫
      pullback.fst (localProjection j) (localProjection j)=
      Spec.map (CommRingCat.ofHom (ThetaPairGalois.L (R:=R j) (S:=S j)).toRingHom) :=
    pullbackSpecIso_inv_fst (R j) (S j) (S j)
  rw [kernelPairSchemeIso_hom]
  simp only [Category.assoc,coprodSpec_inl_assoc,hp]
  rw [←Spec.map_comp,←Spec.map_comp]
  have he : (RingHom.fst (S j) (S j)).comp ((kernelPairRingIso j).toRingHom.comp
      (ThetaPairGalois.L (R:=R j) (S:=S j)).toRingHom)=RingHom.id (S j) := by
    apply RingHom.ext
    intro s
    exact congrArg Prod.fst (ThetaPairGalois.phi_L (data j) s)
  change Spec.map (CommRingCat.ofHom ((RingHom.fst (S j) (S j)).comp ((kernelPairRingIso j).toRingHom.comp
    (ThetaPairGalois.L (R:=R j) (S:=S j)).toRingHom)))=𝟙 _
  rw [he]
  simp
lemma identity_graph_snd (j : Fin 3) :
    coprod.inl ≫ (kernelPairSchemeIso j).hom ≫ pullback.snd (localProjection j) (localProjection j)=𝟙 _ := by
  have hp : (pullbackSpecIso (R j) (S j) (S j)).inv ≫
      pullback.snd (localProjection j) (localProjection j)=
      Spec.map (CommRingCat.ofHom (ThetaPairGalois.N (R:=R j) (S:=S j)).toRingHom) :=
    pullbackSpecIso_inv_snd (R j) (S j) (S j)
  rw [kernelPairSchemeIso_hom]
  simp only [Category.assoc,coprodSpec_inl_assoc,hp]
  rw [←Spec.map_comp,←Spec.map_comp]
  have he : (RingHom.fst (S j) (S j)).comp ((kernelPairRingIso j).toRingHom.comp
      (ThetaPairGalois.N (R:=R j) (S:=S j)).toRingHom)=RingHom.id (S j) := by
    apply RingHom.ext
    intro s
    exact congrArg Prod.fst (ThetaPairGalois.phi_N (data j) s)
  change Spec.map (CommRingCat.ofHom ((RingHom.fst (S j) (S j)).comp ((kernelPairRingIso j).toRingHom.comp
    (ThetaPairGalois.N (R:=R j) (S:=S j)).toRingHom)))=𝟙 _
  rw [he]
  simp
lemma involution_graph_fst (j : Fin 3) :
    coprod.inr ≫ (kernelPairSchemeIso j).hom ≫ pullback.fst (localProjection j) (localProjection j)=𝟙 _ := by
  have hp : (pullbackSpecIso (R j) (S j) (S j)).inv ≫
      pullback.fst (localProjection j) (localProjection j)=
      Spec.map (CommRingCat.ofHom (ThetaPairGalois.L (R:=R j) (S:=S j)).toRingHom) :=
    pullbackSpecIso_inv_fst (R j) (S j) (S j)
  rw [kernelPairSchemeIso_hom]
  simp only [Category.assoc,coprodSpec_inr_assoc,hp]
  rw [←Spec.map_comp,←Spec.map_comp]
  have he : (RingHom.snd (S j) (S j)).comp ((kernelPairRingIso j).toRingHom.comp
      (ThetaPairGalois.L (R:=R j) (S:=S j)).toRingHom)=RingHom.id (S j) := by
    apply RingHom.ext
    intro s
    exact congrArg Prod.snd (ThetaPairGalois.phi_L (data j) s)
  change Spec.map (CommRingCat.ofHom ((RingHom.snd (S j) (S j)).comp ((kernelPairRingIso j).toRingHom.comp
    (ThetaPairGalois.L (R:=R j) (S:=S j)).toRingHom)))=𝟙 _
  rw [he]
  simp
lemma involution_graph_snd (j : Fin 3) :
    coprod.inr ≫ (kernelPairSchemeIso j).hom ≫ pullback.snd (localProjection j) (localProjection j)=
      Spec.map (CommRingCat.ofHom (ThetaInvolutionChart.nn j).toRingHom) := by
  have hp : (pullbackSpecIso (R j) (S j) (S j)).inv ≫
      pullback.snd (localProjection j) (localProjection j)=
      Spec.map (CommRingCat.ofHom (ThetaPairGalois.N (R:=R j) (S:=S j)).toRingHom) :=
    pullbackSpecIso_inv_snd (R j) (S j) (S j)
  rw [kernelPairSchemeIso_hom]
  simp only [Category.assoc,coprodSpec_inr_assoc,hp]
  rw [←Spec.map_comp,←Spec.map_comp]
  have he : (RingHom.snd (S j) (S j)).comp ((kernelPairRingIso j).toRingHom.comp
      (ThetaPairGalois.N (R:=R j) (S:=S j)).toRingHom)=(ThetaInvolutionChart.nn j).toRingHom := by
    apply RingHom.ext
    intro s
    exact congrArg Prod.snd (ThetaPairGalois.phi_N (data j) s)
  change Spec.map (CommRingCat.ofHom ((RingHom.snd (S j) (S j)).comp ((kernelPairRingIso j).toRingHom.comp
    (ThetaPairGalois.N (R:=R j) (S:=S j)).toRingHom)))=_
  rw [he]
end FourCorner.ThetaActualQuotient
#print axioms FourCorner.ThetaActualQuotient.invariantIso
#print axioms FourCorner.ThetaActualQuotient.invariant_universal
#print axioms FourCorner.ThetaActualQuotient.kernelPairSchemeIso
#print axioms FourCorner.ThetaActualQuotient.identity_graph_fst
#print axioms FourCorner.ThetaActualQuotient.identity_graph_snd
#print axioms FourCorner.ThetaActualQuotient.involution_graph_fst
#print axioms FourCorner.ThetaActualQuotient.involution_graph_snd
