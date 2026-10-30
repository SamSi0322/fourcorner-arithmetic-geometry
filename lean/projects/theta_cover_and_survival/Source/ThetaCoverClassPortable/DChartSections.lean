import ThetaCoverClassPortable.DUniformRiemannRoch
import ThetaCoverClassPortable.DUnboundedGeometricSections
import ThetaCoverClassPortable.DGeometricNativeModel
import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
namespace FourCorner.DRationalInputs
open ThetaLiteralModels AlgebraicGeometry.RelPicard

/-- REAL finite-etale extension and all-geometric-fibre RR chart sections for
original D/Q. Every map, model, genus, place and divisor equation is derived;
HasChartSections is NOT a caller input. -/
theorem actual_finiteEtale_HasChartSections :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra ℚ R') (_ : Module.Finite ℚ R')
      (_ : Algebra.Etale ℚ R') (_ : Module.FaithfullyFlat ℚ R')
      (_ : IsNoetherianRing R') (_ : _root_.IsReduced R')
      (n : ℕ) (γ : Fin n → Fin (7-3) → SchemeHomOver (𝟙 _) (SmoothProperCurve.baseChange ℚ toBase R')),
      HasChartSections (g:=3) (r:=7) (SmoothProperCurve.baseChange ℚ toBase R') γ := by
  classical
  obtain ⟨R',_,_,_,_,_,_,_,N,hN,σ,hσ⟩ := actual_unbounded_geometric_sections 7
  let cR := SmoothProperCurve.baseChange ℚ toBase R'
  let E := (Fintype.equivFin (Fin (7-3) → Fin N)).symm
  let γ := fun i j => σ (E i j)
  refine ⟨R',inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,Fintype.card (Fin (7-3) → Fin N),γ,?_⟩
  intro K _ _ ξ
  let y := ξ ≫ SmoothProperCurve.specMap ℚ R'
  obtain ⟨L,_,_,M,e,he⟩ := actual_geometric_native_model y
  let b := pullbackLeftPullbackSndIso toBase (SmoothProperCurve.specMap ℚ R') ξ
  let eR : M.C ≅ pullback cR ξ := e ≪≫ b.symm
  have hb : b.inv ≫ pullback.snd cR ξ=pullback.snd toBase y := by
    simpa only [b,cR,SmoothProperCurve.baseChange] using
      pullbackLeftPullbackSndIso_inv_snd_snd toBase (SmoothProperCurve.specMap ℚ R') ξ
  have heR : eR.hom ≫ pullback.snd cR ξ=M.toBase := by
    calc eR.hom ≫ pullback.snd cR ξ = e.hom ≫ (b.inv ≫ pullback.snd cR ξ) := by
          simp only [eR,Iso.trans_hom,Category.assoc,Iso.symm_hom]
      _ = e.hom ≫ pullback.snd toBase y := congrArg (e.hom ≫ ·) hb
      _ = M.toBase := he
  obtain ⟨Kc,hRR⟩ := DUniformRiemannRoch.rr_three y M e he
  refine ⟨L,inferInstance,inferInstance,M,eR,heR,⟨Kc,hRR⟩,?_⟩
  intro D hDeff hdeg
  letI := M.isIntegral
  letI := M.smooth
  letI : IsCurveOver K L := isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    M.toBase M.ffEquiv M.ffEquiv_algebraMap
  let p (j : Fin N) : SchemeHomOver (𝟙 _) M.toBase :=
    ⟨(sectionFibrePoint (σ j) ξ).1 ≫ eR.inv,by
      rw [Category.assoc,←heR,eR.inv_hom_id_assoc]
      exact (sectionFibrePoint (σ j) ξ).2⟩
  let place (j : Fin N) : Place K L := M.pointEquivPlace (p j)
  have hp : Function.Injective p := by
    intro i j hij
    apply hσ K ξ
    have h1 := congrArg Subtype.val hij
    have h2 := (cancel_mono eR.inv).mp h1
    have h3 := congrArg (fun f : Spec (.of K) ⟶ pullback cR ξ => f ≫ pullback.fst cR ξ) h2
    simpa only [cR,sectionFibrePoint,pullback.lift_fst] using h3
  have hplace : Function.Injective place := M.pointEquivPlace.injective.comp hp
  let S : Finset (Place K L) := Finset.univ.image place
  have hS : ∀ v ∈ S,v.deg=1 := fun v _ => IsCurveOver.deg_eq_one_of_isAlgClosed v
  have hcard : 7+1≤S.card := by
    have hN' : 7+1≤N := by omega
    simpa only [S,Finset.card_image_of_injective _ hplace,Finset.card_univ,Fintype.card_fin] using hN'
  obtain ⟨f,hfi,hfS,hell⟩ :=
    P2MW.S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card.solution
      hRR (by norm_num : 2*3≤7+1) S hS hcard D hdeg
  have hf : ∀ j,∃ a : Fin N,place a=f j := by
    intro j
    simpa only [S,Finset.mem_image,Finset.mem_univ,true_and] using hfS j
  choose a ha using hf
  refine ⟨E.symm a,?_⟩
  have hsum : (∑ j : Fin (7-3),Finsupp.single
      (M.pointEquivPlace ⟨(sectionFibrePoint (γ (E.symm a) j) ξ).1 ≫ eR.inv,by
        rw [Category.assoc,←heR,eR.inv_hom_id_assoc]
        exact (sectionFibrePoint (γ (E.symm a) j) ξ).2⟩) (1:ℤ)) =
      ∑ j : Fin (7-3),Finsupp.single (f j) (1:ℤ) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    change place (E (E.symm a) j)=f j
    rw [Equiv.apply_symm_apply,ha]
  simpa only [hsum] using hell

#print axioms actual_finiteEtale_HasChartSections
end FourCorner.DRationalInputs
