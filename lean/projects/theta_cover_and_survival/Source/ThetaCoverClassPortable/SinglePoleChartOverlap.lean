import ThetaCoverClassPortable.SinglePoleChartAlgebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
namespace FourCorner.NativeSinglePoleCharts
open CurveModel
universe u
variable {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
  (t : L) [Fact (t≠0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
  {X : Scheme.{u}} (i : X ≅ glued K t)

theorem mem_U_iff (x : X) : x∈U t i ↔ i.hom x∈Set.range (ι₀ K t).base := by
  constructor
  · rintro ⟨p,_,hp⟩
    refine ⟨p,?_⟩
    change i.inv (ι₀ K t p)=x at hp
    rw [← hp]
    exact (congrArg (fun g : glued K t ⟶ glued K t => g (ι₀ K t p)) i.inv_hom_id).symm
  · rintro ⟨p,hp⟩
    exact ⟨p,trivial,by change i.inv (ι₀ K t p)=x; rw [hp]; exact congrArg (fun g : X ⟶ X => g x) i.hom_inv_id⟩

theorem mem_V_iff (x : X) : x∈V t i ↔ i.hom x∈Set.range (ιInf K t).base := by
  constructor
  · rintro ⟨p,_,hp⟩
    refine ⟨p,?_⟩
    change i.inv (ιInf K t p)=x at hp
    rw [← hp]
    exact (congrArg (fun g : glued K t ⟶ glued K t => g (ιInf K t p)) i.inv_hom_id).symm
  · rintro ⟨p,hp⟩
    exact ⟨p,trivial,by change i.inv (ιInf K t p)=x; rw [hp]; exact congrArg (fun g : X ⟶ X => g x) i.hom_inv_id⟩

theorem basicOpen_fSection : X.basicOpen (fSection t i)=U t i ⊓ V t i := by
  change X.basicOpen ((jZero t i).appIso ⊤ |>.inv <| secTop K (chartRing K ({t}:Set L)) (tChart K t))=_
  rw [← Scheme.image_basicOpen]
  have he : (X₀ K t).basicOpen (secTop K (chartRing K ({t}:Set L)) (tChart K t))=
      jZero t i ⁻¹ᵁ V t i := by
    ext p
    change p∈(X₀ K t).basicOpen (secTop K (chartRing K ({t}:Set L)) (tChart K t)) ↔ jZero t i p∈V t i
    rw [mem_basicOpen_secTop]
    rw [mem_V_iff]
    have hh : i.hom (jZero t i p)=ι₀ K t p :=
      congrArg (fun g : glued K t ⟶ glued K t => g (ι₀ K t p)) i.inv_hom_id
    rw [hh,ι₀_mem_range_ιInf_iff]
  rw [he,Scheme.Hom.image_preimage_eq_opensRange_inf,← Scheme.Hom.image_top_eq_opensRange]
  rfl

theorem basicOpen_gSection : X.basicOpen (gSection t i)=U t i ⊓ V t i := by
  change X.basicOpen ((jInfinity t i).appIso ⊤ |>.inv <| secTop K (chartRing K ({t⁻¹}:Set L)) (tInvChart K t))=_
  rw [← Scheme.image_basicOpen]
  have he : (XInf K t).basicOpen (secTop K (chartRing K ({t⁻¹}:Set L)) (tInvChart K t))=
      jInfinity t i ⁻¹ᵁ U t i := by
    ext p
    change p∈(XInf K t).basicOpen (secTop K (chartRing K ({t⁻¹}:Set L)) (tInvChart K t)) ↔ jInfinity t i p∈U t i
    rw [mem_basicOpen_secTop]
    rw [mem_U_iff]
    have hh : i.hom (jInfinity t i p)=ιInf K t p :=
      congrArg (fun g : glued K t ⟶ glued K t => g (ιInf K t p)) i.inv_hom_id
    rw [hh,ιInf_mem_range_ι₀_iff]
  rw [he,Scheme.Hom.image_preimage_eq_opensRange_inf,← Scheme.Hom.image_top_eq_opensRange]
  exact inf_comm _ _

end FourCorner.NativeSinglePoleCharts
