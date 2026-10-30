import ThetaActualPoints
import ThetaPointAPI
import ThetaHomogeneousEvaluation
import ThetaProjection
noncomputable section
namespace FourCorner.ThetaBoundary
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaActualPoints
universe u
variable {k : Type u} [Field k] [CharZero k]
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
abbrev sg := grading (sourceEquation k) (source_homogeneous k)
abbrev sc (a : Fin 5) := coordinate (sourceEquation k) (source_homogeneous k) a
abbrev ar (j : Fin 5) := affineRing (sourceEquation k) j
abbrev ev (j : Fin 5) := ThetaHomogeneousEvaluation.affineEvaluation (sourceEquation k) j
def ax (j : Fin 5) (a : Fin 4) : ar (k:=k) j := Ideal.Quotient.mk _ (X a)
def normalized (j : Fin 5) (x : Fin 4 → k) (a : Fin 5) : k :=
  if a=j then 1 else x (ThetaAmbientChart.drop 4 j a)
lemma ev_X (j a : Fin 5) (f : ar (k:=k) j →ₐ[k] k) :
    f (ev j (X a))=normalized j (fun b=>f (ax j b)) a := by
  simp only [ev,ThetaHomogeneousEvaluation.affineEvaluation,RingHom.comp_apply,ThetaAmbientChart.dehom,coe_eval₂Hom,eval₂_X,normalized]
  split_ifs <;> simp [ax]
lemma evaluation (j : Fin 5) (f : ar (k:=k) j →ₐ[k] k) (p : MvPolynomial (Fin 5) k) :
    MvPolynomial.aeval (normalized j (fun b=>f (ax j b))) p=f (ev j p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [aeval_C,ev,ThetaHomogeneousEvaluation.affineEvaluation,RingHom.comp_apply,
      ThetaAmbientChart.dehom,coe_eval₂Hom,eval₂_C]
    change algebraMap k k a=f (algebraMap k (ar j) a)
    exact (f.commutes a).symm
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p a hp => simp only [map_mul,hp,aeval_X,ev_X]
lemma coordinates (j : Fin 5) (f : ar (k:=k) j →ₐ[k] k) :
    ThetaProjectiveCoordinates.Source
      (normalized j (fun b=>f (ax j b)) 0) (normalized j (fun b=>f (ax j b)) 1)
      (normalized j (fun b=>f (ax j b)) 2) (normalized j (fun b=>f (ax j b)) 3)
      (normalized j (fun b=>f (ax j b)) 4) := by
  apply (source_eval k _).mp
  intro a
  rw [evaluation]
  have hz : ev j (sourceEquation k a)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a,rfl⟩)
  rw [hz,map_zero]
def tOpen := Proj.basicOpen (sg (k:=k)) (sc (k:=k) 4)
lemma zero_T (j : Fin 5) (f : ar (k:=k) j →ₐ[k] k)
    (hb : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (chartIso (sourceEquation k) (source_homogeneous k) j).inv ≫
      (Proj.basicOpen (sg (k:=k)) (sc (k:=k) j)).ι) ⁻¹ᵁ tOpen=⊥) :
    normalized j (fun b=>f (ax j b)) 4=0 := by
  have hpre:=ThetaHomogeneousEvaluation.point_preimage (sourceEquation k) (source_homogeneous k)
    j f (X 4) (isHomogeneous_X k 4) one_pos
  change _=PrimeSpectrum.basicOpen (f (ev j (X 4))) at hpre
  have hz : PrimeSpectrum.basicOpen (f (ev j (X 4)))=⊥ := hpre.symm.trans hb
  exact (ev_X j 4 f) ▸ isNilpotent_iff_eq_zero.mp ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp hz)
lemma boundary_factor (p : Spec (.of k) ⟶ C k) (hp : p ≫ cToBase k=𝟙 _) (hb : p ⁻¹ᵁ tOpen=⊥) :
    ∃ f : ar (k:=k) 3 →ₐ[k] k,
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        (chartIso (sourceEquation k) (source_homogeneous k) 3).inv ≫
        (Proj.basicOpen (sg (k:=k)) (sc (k:=k) 3)).ι=p ∧ f (ax 3 3)=0 := by
  have hp' : p ≫ cToBase k=Spec.map (CommRingCat.ofHom (algebraMap k k)) := by simpa using hp
  obtain ⟨j,f,hf⟩:=ThetaPointAPI.point_affine_algebra (sourceEquation k) (source_homogeneous k) p hp'
  have ht:=zero_T j f (by rw [hf];exact hb)
  have hs:=coordinates j f
  have hz : normalized j (fun b=>f (ax j b)) 3≠0 := by
    intro hz
    obtain ⟨h0,h1,h2⟩:=ThetaProjectiveCoordinates.no_base_line hs hz ht
    have hall (a : Fin 5) : normalized j (fun b=>f (ax j b)) a=0 := by fin_cases a <;> assumption
    have hh:=hall j
    simpa [normalized] using hh
  have hpre:=ThetaHomogeneousEvaluation.point_preimage (sourceEquation k) (source_homogeneous k)
    j f (X 3) (isHomogeneous_X k 3) one_pos
  have hU : p ⁻¹ᵁ Proj.basicOpen (sg (k:=k)) (sc (k:=k) 3)=⊤ := by
    rw [←hf,hpre,ev_X]
    have he:=PrimeSpectrum.basicOpen_mul (normalized j (fun b=>f (ax j b)) 3)
      (normalized j (fun b=>f (ax j b)) 3)⁻¹
    rw [mul_inv_cancel₀ hz,PrimeSpectrum.basicOpen_one] at he
    exact top_le_iff.mp (he.trans_le inf_le_left)
  let U:=Proj.basicOpen (sg (k:=k)) (sc (k:=k) 3)
  have hr : Set.range p⊆Set.range U.ι := by
    rintro _ ⟨x,rfl⟩
    refine ⟨⟨p x,?_⟩,rfl⟩
    change x∈p ⁻¹ᵁ U
    rw [hU];trivial
  let q:=IsOpenImmersion.lift U.ι p hr
  have hq : q ≫ U.ι=p:=IsOpenImmersion.lift_fac U.ι p hr
  obtain ⟨g,hg⟩:=ThetaPointAPI.algebra_of_chart_factor (sourceEquation k) (source_homogeneous k) p hp' 3 q hq
  refine ⟨g,hg,?_⟩
  have ht':=zero_T 3 g (by rw [hg];exact hb)
  have hd : ThetaAmbientChart.drop 4 (3:Fin 5) 4=3 := by decide
  simpa [normalized,hd] using ht'
lemma chart_hom_ext (f g : ar (k:=k) 3 →ₐ[k] k)
    (h : ∀ a,f (ax 3 a)=g (ax 3 a)) : f=g := by
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a => exact (f.commutes a).trans (g.commutes a).symm
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p a hp => simpa only [map_mul,ax] using congrArg₂ (·*·) hp (h a)

lemma boundaryPoint_boundary (e : Fin 3 → Bool) : boundaryPoint (k:=k) e ⁻¹ᵁ tOpen=⊥ := by
  have hpre:=ThetaHomogeneousEvaluation.point_preimage (sourceEquation k) (source_homogeneous k)
    3 (boundaryEvaluation (k:=k) e) (X 4) (isHomogeneous_X k 4) one_pos
  have hd : ThetaAmbientChart.drop 4 (3:Fin 5) 4=3 := by decide
  have hv : boundaryEvaluation (k:=k) e (ev 3 (X 4))=0 := by
    simp [ev,ThetaHomogeneousEvaluation.affineEvaluation,ThetaAmbientChart.dehom,hd,sourceValues]
  change _=PrimeSpectrum.basicOpen _ at hpre
  rw [hv,PrimeSpectrum.basicOpen_zero] at hpre
  exact hpre
/-- Exhaustive classification of the actual rational scheme boundary, with the structural map retained. -/
theorem boundary_iff (p : Spec (.of k) ⟶ C k) (hp : p ≫ cToBase k=𝟙 _) :
    p ⁻¹ᵁ tOpen=⊥ ↔ ∃ e : Fin 3 → Bool,p=boundaryPoint e := by
  constructor
  · intro hb
    obtain ⟨f,hf,ht⟩:=boundary_factor p hp hb
    have hs:=coordinates 3 f
    have hd0 : ThetaAmbientChart.drop 4 (3:Fin 5) 0=0 := by decide
    have hd1 : ThetaAmbientChart.drop 4 (3:Fin 5) 1=1 := by decide
    have hd2 : ThetaAmbientChart.drop 4 (3:Fin 5) 2=2 := by decide
    have hd4 : ThetaAmbientChart.drop 4 (3:Fin 5) 4=3 := by decide
    have hsq : ∀ a : Fin 3,f (ax 3 a.castSucc)^2=1 := by
      simp [ThetaProjectiveCoordinates.Source,normalized,hd0,hd1,hd2,hd4,ht] at hs
      intro a
      fin_cases a
      · exact sq_eq_one_iff.mpr hs.1
      · exact sq_eq_one_iff.mpr hs.2.1
      · exact sq_eq_one_iff.mpr hs.2.2
    have he : ∀ a : Fin 3,∃ b : Bool,f (ax 3 a.castSucc)=sign (k:=k) b := by
      intro a
      rcases sq_eq_one_iff.mp (hsq a) with h|h
      · exact ⟨true,by simpa [sign] using h⟩
      · exact ⟨false,by simpa [sign] using h⟩
    let e : Fin 3 → Bool:=fun a=>Classical.choose (he a)
    have hes (a : Fin 3) : f (ax 3 a.castSucc)=sign (k:=k) (e a) := Classical.choose_spec (he a)
    have hfg : f=boundaryEvaluation e := by
      apply chart_hom_ext
      intro a
      fin_cases a
      · simpa [ax,boundaryEvaluation_X,sourceValues] using hes 0
      · simpa [ax,boundaryEvaluation_X,sourceValues] using hes 1
      · simpa [ax,boundaryEvaluation_X,sourceValues] using hes 2
      · simpa [ax,boundaryEvaluation_X,sourceValues] using ht
    refine ⟨e,?_⟩
    rw [←hf,hfg]
    rfl
  · rintro ⟨e,rfl⟩
    exact boundaryPoint_boundary e

def RationalBoundary := {p : Spec (.of k) ⟶ C k // p ≫ cToBase k=𝟙 _ ∧ p ⁻¹ᵁ tOpen=⊥}
def boundaryEquiv : (Fin 3 → Bool) ≃ RationalBoundary (k:=k) where
  toFun e := ⟨boundaryPoint e,boundaryPoint_over e,boundaryPoint_boundary e⟩
  invFun p := Classical.choose ((boundary_iff p.1 p.2.1).mp p.2.2)
  left_inv e := by
    apply boundaryPoint_injective (k:=k)
    exact (Classical.choose_spec ((boundary_iff (boundaryPoint e) (boundaryPoint_over e)).mp
      (boundaryPoint_boundary e))).symm
  right_inv p := by
    apply Subtype.ext
    exact (Classical.choose_spec ((boundary_iff p.1 p.2.1).mp p.2.2)).symm
/-- The full actual k-rational boundary has precisely eight points. -/
theorem rational_boundary_card : Nat.card (RationalBoundary (k:=k))=8 := by
  rw [←Nat.card_congr (boundaryEquiv (k:=k))]
  simp
end FourCorner.ThetaBoundary
#print axioms FourCorner.ThetaBoundary.boundary_iff

#print axioms FourCorner.ThetaBoundary.rational_boundary_card
