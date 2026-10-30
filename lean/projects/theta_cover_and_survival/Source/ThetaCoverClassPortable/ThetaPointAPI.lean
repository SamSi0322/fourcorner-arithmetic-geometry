import ThetaCoverClassPortable.ThetaModelBase
noncomputable section
namespace FourCorner.ThetaPointAPI
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open ThetaProjectiveModel
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {n : ℕ} [NeZero n] {ι : Type*} {d : ℕ}
variable (v : ι → ThetaAmbientChart.ambient k n) (hv : ∀ a,(v a).IsHomogeneous d)
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
theorem point_chart_factor (p : Spec (.of L) ⟶ curve v hv) :
    ∃ j : Fin (n+1), ∃ q : Spec (.of L) ⟶ (Proj.basicOpen (grading v hv) (coordinate v hv j)).toScheme,
      q ≫ (Proj.basicOpen (grading v hv) (coordinate v hv j)).ι=p := by
  let x : Spec (.of L):=Classical.choice inferInstance
  have hx : p x∈⨆ j : Fin (n+1), Proj.basicOpen (grading v hv) (coordinate v hv j) := by
    rw [opens_cover v hv];trivial
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U:=Proj.basicOpen (grading v hv) (coordinate v hv j)
  have hr : Set.range p⊆Set.range U.ι := by
    rintro y ⟨z,rfl⟩
    have hzx : z=x:=Subsingleton.elim _ _
    exact ⟨⟨p z,by simpa only [hzx] using hj⟩,rfl⟩
  exact ⟨j,IsOpenImmersion.lift U.ι p hr,IsOpenImmersion.lift_fac U.ι p hr⟩

/-- An arbitrary OVER-k point is obtained from the actual affine quotient in
one actual standard chart. k-linearity is derived from the structural map. -/
theorem algebra_of_chart_factor (p : Spec (.of L) ⟶ curve v hv)
    (hp : p ≫ toBase v hv=Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (j : Fin (n+1)) (q : Spec (.of L) ⟶ (Proj.basicOpen (grading v hv) (coordinate v hv j)).toScheme)
    (hq : q ≫ (Proj.basicOpen (grading v hv) (coordinate v hv j)).ι=p) :
    ∃ f : affineRing v j →ₐ[k] L,
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (chartIso v hv j).inv ≫
        (Proj.basicOpen (grading v hv) (coordinate v hv j)).ι=p := by
  let r:=q ≫ (chartIso v hv j).hom
  let g : affineRing v j →+* L := (Spec.homEquiv r).hom
  have hg : Spec.map (CommRingCat.ofHom g)=r := Spec.homEquiv.symm_apply_apply r
  have hc : Spec.map (CommRingCat.ofHom g) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (affineRing v j)))=Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [hg]
    dsimp only [r]
    rw [Category.assoc,←ThetaModelBase.chart_over_base v hv j]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rw [←Category.assoc,hq,hp]
  have hgk : g.comp (algebraMap k (affineRing v j))=algebraMap k L := by
    have hh : CommRingCat.ofHom (g.comp (algebraMap k (affineRing v j)))=
        CommRingCat.ofHom (algebraMap k L) := by
      apply Spec.map_injective
      simpa only [CommRingCat.ofHom_comp,Spec.map_comp,CommRingCat.ofHom_id,Spec.map_id] using hc
    exact congrArg CommRingCat.Hom.hom hh
  let f : affineRing v j →ₐ[k] L := {g with commutes':=fun a=>RingHom.congr_fun hgk a}
  refine ⟨f,?_⟩
  change Spec.map (CommRingCat.ofHom g) ≫ _ ≫ _=p
  rw [hg]
  simp only [r,Category.assoc,Iso.hom_inv_id_assoc]
  exact hq

theorem point_affine_algebra (p : Spec (.of L) ⟶ curve v hv)
    (hp : p ≫ toBase v hv=Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    ∃ j : Fin (n+1), ∃ f : affineRing v j →ₐ[k] L,
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (chartIso v hv j).inv ≫
        (Proj.basicOpen (grading v hv) (coordinate v hv j)).ι=p := by
  obtain ⟨j,q,hq⟩:=point_chart_factor v hv p
  obtain ⟨f,hf⟩:=algebra_of_chart_factor v hv p hp j q hq
  exact ⟨j,f,hf⟩


end FourCorner.ThetaPointAPI
#print axioms FourCorner.ThetaPointAPI.point_affine_algebra
