import CriticalProjectiveSmooth
import CriticalTwoChartCover

noncomputable section
namespace FourCorner.CriticalExtensionPoints
open AlgebraicGeometry CategoryTheory CriticalProj23 CriticalStandardCharts
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem point_chart_factor (i : k) (p : Spec (.of L) ⟶ criticalCurve i) :
    ∃ j : Fin 4, ∃ q : Spec (.of L) ⟶ (Proj.basicOpen (criticalGrading i) (coordinate i j)).toScheme,
      q ≫ (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι=p := by
  let x : Spec (.of L):=Classical.choice inferInstance
  have hx : p x∈⨆ j : Fin 4, Proj.basicOpen (criticalGrading i) (coordinate i j) := by
    rw [coordinate_opens_cover];trivial
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U:=Proj.basicOpen (criticalGrading i) (coordinate i j)
  have hr : Set.range p⊆Set.range U.ι := by
    rintro y ⟨z,rfl⟩
    have hzx : z=x:=Subsingleton.elim _ _
    exact ⟨⟨p z,by simpa only [hzx] using hj⟩,rfl⟩
  exact ⟨j,IsOpenImmersion.lift U.ι p hr,IsOpenImmersion.lift_fac U.ι p hr⟩

/-- An arbitrary OVER-k point is obtained from the actual affine quotient in
one actual standard chart. k-linearity is derived from the structural map. -/
theorem algebra_of_chart_factor (i : k) (p : Spec (.of L) ⟶ criticalCurve i)
    (hp : p ≫ criticalToSpec i=Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (j : Fin 4) (q : Spec (.of L) ⟶ (Proj.basicOpen (criticalGrading i) (coordinate i j)).toScheme)
    (hq : q ≫ (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι=p) :
    ∃ f : affineRing i j →ₐ[k] L,
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (chartIso i j).inv ≫
        (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι=p := by
  let r:=q ≫ (chartIso i j).hom
  let g : affineRing i j →+* L := (Spec.homEquiv r).hom
  have hg : Spec.map (CommRingCat.ofHom g)=r := Spec.homEquiv.symm_apply_apply r
  have hc : Spec.map (CommRingCat.ofHom g) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (affineRing i j)))=Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [hg]
    dsimp only [r]
    rw [Category.assoc,←CriticalChartBase.chart_over_base i j]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rw [←Category.assoc,hq,hp]
  have hgk : g.comp (algebraMap k (affineRing i j))=algebraMap k L := by
    have hh : CommRingCat.ofHom (g.comp (algebraMap k (affineRing i j)))=
        CommRingCat.ofHom (algebraMap k L) := by
      apply Spec.map_injective
      simpa only [CommRingCat.ofHom_comp,Spec.map_comp,CommRingCat.ofHom_id,Spec.map_id] using hc
    exact congrArg CommRingCat.Hom.hom hh
  let f : affineRing i j →ₐ[k] L := {g with commutes':=fun a=>RingHom.congr_fun hgk a}
  refine ⟨f,?_⟩
  change Spec.map (CommRingCat.ofHom g) ≫ _ ≫ _=p
  rw [hg]
  simp only [r,Category.assoc,Iso.hom_inv_id_assoc]
  exact hq

theorem point_affine_algebra (i : k) (p : Spec (.of L) ⟶ criticalCurve i)
    (hp : p ≫ criticalToSpec i=Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    ∃ j : Fin 4, ∃ f : affineRing i j →ₐ[k] L,
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (chartIso i j).inv ≫
        (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι=p := by
  obtain ⟨j,q,hq⟩:=point_chart_factor i p
  obtain ⟨f,hf⟩:=algebra_of_chart_factor i p hp j q hq
  exact ⟨j,f,hf⟩

/-- Exact extraction of homogeneous coordinates from every genuine OVER-k
Scheme point. No tuple-to-global-point implication is assumed. -/
theorem point_coordinates (i : k) (p : Spec (.of L) ⟶ criticalCurve i)
    (hp : p ≫ criticalToSpec i=Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    ∃ (j : Fin 4) (f : affineRing i j →ₐ[k] L),
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (chartIso i j).inv ≫
        (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι=p ∧
      CriticalElliptic23.CriticalCoordinates (algebraMap k L i)
        (CriticalChartSmooth.normalizedVector j (fun a=>f (CriticalChartJacobian.ax i j a))) ∧
      CriticalChartSmooth.normalizedVector j (fun a=>f (CriticalChartJacobian.ax i j a)) j=1 := by
  obtain ⟨j,f,hf⟩:=point_affine_algebra i p hp
  refine ⟨j,f,hf,?_,CriticalChartSmooth.normalizedVector_self j _⟩
  exact CriticalChartSmooth.field_point_coordinates i j L f
end FourCorner.CriticalExtensionPoints
#print axioms FourCorner.CriticalExtensionPoints.point_affine_algebra
#print axioms FourCorner.CriticalExtensionPoints.point_coordinates
