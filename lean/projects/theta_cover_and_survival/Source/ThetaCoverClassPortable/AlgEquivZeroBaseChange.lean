import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
namespace FourCorner.AlgEquivZeroBaseChange
open RelPicard
variable {k l : Type} [Field k] [Field l] {X : Scheme}
    (a : X ⟶ Spec (.of k)) (b : Spec (.of l) ⟶ Spec (.of k))

/-- True families witnessing algebraic equivalence to zero remain true
after constant-field base change. All fibre comparison maps are the
literal categorical pullback maps; no all-fibre predicate is assumed. -/
theorem baseChange {L : X.Modules} (hL : IsAlgEquivZero a L) :
    IsAlgEquivZero (pullback.snd a b) ((Scheme.Modules.pullback (pullback.fst a b)).obj L) := by
  obtain ⟨T,h,hft,hgi,M,hM,t₀,t₁,⟨e₀⟩,⟨e₁⟩⟩ := hL
  let a' := pullback.snd a b
  let h' := pullback.snd h b
  let g : pullback a' h' ⟶ pullback a h :=
    pullback.lift (pullback.fst a' h' ≫ pullback.fst a b)
      (pullback.snd a' h' ≫ pullback.fst h b) (by
        rw [Category.assoc,pullback.condition,←Category.assoc,pullback.condition]
        simp only [h',Category.assoc,pullback.condition])
  let u (t : SchemeHomOver (𝟙 (Spec (.of k))) h) : SchemeHomOver (𝟙 (Spec (.of l))) h' :=
    ⟨pullback.lift (b≫t.val) (𝟙 _) (by rw [Category.assoc,t.property,Category.comp_id,Category.id_comp]),by
      rw [pullback.lift_snd]⟩
  let e : pullback a' (𝟙 (Spec (.of l))) ⟶ pullback a (𝟙 (Spec (.of k))) :=
    pullback.lift (pullback.fst a' (𝟙 _) ≫ pullback.fst a b)
      (pullback.snd a' (𝟙 _) ≫ b) (by
        rw [Category.assoc,pullback.condition,←Category.assoc,pullback.condition,Category.comp_id,Category.comp_id])
  have hs (t : SchemeHomOver (𝟙 (Spec (.of k))) h) :
      baseChangeSnd a' (u t) ≫ g=e≫baseChangeSnd a t := by
    apply pullback.hom_ext
    · simp only [g,e,u,baseChangeSnd,Category.assoc,pullback.lift_fst,pullback.lift_fst_assoc,Category.comp_id]
    · simp only [g,e,u,baseChangeSnd,Category.assoc,pullback.lift_snd,pullback.lift_snd_assoc,
        pullback.lift_fst,pullback.lift_fst_assoc,Category.comp_id,Category.id_comp]
  have he : e≫pullback.fst a (𝟙 _)=pullback.fst a' (𝟙 _)≫pullback.fst a b := by
    simp only [e,pullback.lift_fst]
  refine ⟨pullback h b,h',inferInstance,inferInstance,(Scheme.Modules.pullback g).obj M,
    hM.pullback g,u t₀,u t₁,⟨?_⟩,⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hs t₀)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback e).mapIso e₀ ≪≫ Scheme.Modules.pullbackUnitIso e
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hs t₁)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback e).mapIso e₁ ≪≫
      (Scheme.Modules.pullbackComp _ _).app L ≪≫
      (Scheme.Modules.pullbackCongr he).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm

#print axioms baseChange
end FourCorner.AlgEquivZeroBaseChange
