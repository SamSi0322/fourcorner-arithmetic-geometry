import ThetaCoverClassPortable.ThetaBoundary
import ThetaCoverClassPortable.ThetaActualPoints
import ThetaCoverClassPortable.ThetaPointAPI
import ThetaCoverClassPortable.ThetaHomogeneousEvaluation
import ThetaCoverClassPortable.ThetaProjection
noncomputable section
namespace FourCorner.ThetaCSchemeBoundaryFinite
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaActualPoints
universe u
variable {k L : Type u} [Field k] [CharZero k] [Field L] [Algebra k L] [CharZero L]
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
def normalized (j : Fin 5) (x : Fin 4 → L) (a : Fin 5) : L :=
  if a=j then 1 else x (ThetaAmbientChart.drop 4 j a)
lemma ev_X (j a : Fin 5) (f : ar (k:=k) j →ₐ[k] L) :
    f (ev j (X a))=normalized j (fun b=>f (ax j b)) a := by
  simp only [ev,ThetaHomogeneousEvaluation.affineEvaluation,RingHom.comp_apply,ThetaAmbientChart.dehom,coe_eval₂Hom,eval₂_X,normalized]
  split_ifs <;> simp [ax]
lemma evaluation (j : Fin 5) (f : ar (k:=k) j →ₐ[k] L) (p : MvPolynomial (Fin 5) k) :
    MvPolynomial.aeval (normalized j (fun b=>f (ax j b))) p=f (ev j p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [aeval_C,ev,ThetaHomogeneousEvaluation.affineEvaluation,RingHom.comp_apply,
      ThetaAmbientChart.dehom,coe_eval₂Hom,eval₂_C]
    change algebraMap k L a=f (algebraMap k (ar j) a)
    exact (f.commutes a).symm
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p a hp => simp only [map_mul,hp,aeval_X,ev_X]
lemma coordinates (j : Fin 5) (f : ar (k:=k) j →ₐ[k] L) :
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
lemma zero_T (j : Fin 5) (f : ar (k:=k) j →ₐ[k] L)
    (hb : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (chartIso (sourceEquation k) (source_homogeneous k) j).inv ≫
      (Proj.basicOpen (sg (k:=k)) (sc (k:=k) j)).ι) ⁻¹ᵁ tOpen=⊥) :
    normalized j (fun b=>f (ax j b)) 4=0 := by
  have hpre:=ThetaHomogeneousEvaluation.point_preimage (sourceEquation k) (source_homogeneous k)
    j f (X 4) (isHomogeneous_X k 4) one_pos
  change _=PrimeSpectrum.basicOpen (f (ev j (X 4))) at hpre
  have hz : PrimeSpectrum.basicOpen (f (ev j (X 4)))=⊥ := hpre.symm.trans hb
  exact (ev_X j 4 f) ▸ isNilpotent_iff_eq_zero.mp ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp hz)
lemma boundary_factor (p : Spec (.of L) ⟶ C k) (hp : p ≫ cToBase k=Spec.map (CommRingCat.ofHom (algebraMap k L))) (hb : p ⁻¹ᵁ tOpen=⊥) :
    ∃ f : ar (k:=k) 3 →ₐ[k] L,
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        (chartIso (sourceEquation k) (source_homogeneous k) 3).inv ≫
        (Proj.basicOpen (sg (k:=k)) (sc (k:=k) 3)).ι=p ∧ f (ax 3 3)=0 := by
  have hp' : p ≫ cToBase k=Spec.map (CommRingCat.ofHom (algebraMap k L)) := by simpa using hp
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
lemma chart_hom_ext (f g : ar (k:=k) 3 →ₐ[k] L)
    (h : ∀ a,f (ax 3 a)=g (ax 3 a)) : f=g := by
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a => exact (f.commutes a).trans (g.commutes a).symm
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p a hp => simpa only [map_mul,ax] using congrArg₂ (·*·) hp (h a)


/-- All field-valued points of the original base-k Proj boundary, including
points with nontrivial residue extensions, come from actual rational supports. -/
theorem boundary_field_factor (p : Spec (.of L) ⟶ C k)
    (hp : p ≫ cToBase k=Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hb : p ⁻¹ᵁ tOpen=⊥) :
    ∃ e : Fin 3 → Bool,p=Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ boundaryPoint e := by
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
  have he : ∀ a : Fin 3,∃ b : Bool,f (ax 3 a.castSucc)=sign (k:=L) b := by
    intro a
    rcases sq_eq_one_iff.mp (hsq a) with h|h
    · exact ⟨true,by simpa [sign] using h⟩
    · exact ⟨false,by simpa [sign] using h⟩
  let e : Fin 3 → Bool:=fun a=>Classical.choose (he a)
  have hes (a : Fin 3) : f (ax 3 a.castSucc)=sign (k:=L) (e a) := Classical.choose_spec (he a)
  have hmapSign (b : Bool) : algebraMap k L (sign (k:=k) b)=sign (k:=L) b := by
    cases b <;> simp [sign]
  have hfg : f=(Algebra.ofId k L).comp (boundaryEvaluation (k:=k) e) := by
    apply chart_hom_ext
    intro a
    simp only [AlgHom.comp_apply,ax,boundaryEvaluation_X]
    fin_cases a
    · change f (ax 3 0)=algebraMap k L (sign (k:=k) (e 0))
      rw [hmapSign];exact hes 0
    · change f (ax 3 1)=algebraMap k L (sign (k:=k) (e 1))
      rw [hmapSign];exact hes 1
    · change f (ax 3 2)=algebraMap k L (sign (k:=k) (e 2))
      rw [hmapSign];exact hes 2
    · change f (ax 3 3)=algebraMap k L 0
      rw [map_zero];exact ht
  refine ⟨e,?_⟩
  rw [←hf,hfg]
  simp only [boundaryPoint,←Category.assoc,←Spec.map_comp]
  rfl


def boundarySupport (e : Fin 3 → Bool) : C ℚ :=
  boundaryPoint (k:=ℚ) e (IsLocalRing.closedPoint ℚ)

/-- The complement is exactly these eight actual rational supports, as a set
of ALL points of the original scheme, not merely a set of QQ-valued maps. -/
theorem boundary_eq_range : ((tOpen (k:=ℚ) : Set (C ℚ))ᶜ)=Set.range boundarySupport := by
  ext x
  constructor
  · intro hx
    let K := (C ℚ).residueField x
    let p : Spec (.of K) ⟶ C ℚ := (C ℚ).fromSpecResidueField x
    let b : ℚ →+* K := (Spec.homEquiv (p ≫ cToBase ℚ)).hom
    letI : Algebra ℚ K := b.toAlgebra
    letI : CharZero K := algebraRat.charZero K
    have hp : p ≫ cToBase ℚ=Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) :=
      (Spec.homEquiv.symm_apply_apply (p ≫ cToBase ℚ)).symm
    have hb : p ⁻¹ᵁ tOpen=⊥ := by
      ext y
      change p y∈tOpen ↔ False
      rw [show p y=x from Scheme.fromSpecResidueField_apply x y]
      exact iff_false_intro hx
    obtain ⟨e,he⟩ := boundary_field_factor p hp hb
    refine ⟨e,?_⟩
    have hh := congrArg (fun f : Spec (.of K) ⟶ C ℚ => f (IsLocalRing.closedPoint K)) he
    rw [show p (IsLocalRing.closedPoint K)=x from Scheme.fromSpecResidueField_apply x _] at hh
    change boundarySupport e=x
    rw [hh]
    apply congrArg (boundaryPoint (k:=ℚ) e)
    exact Subsingleton.elim _ _
  · rintro ⟨e,rfl⟩
    have hb := ThetaBoundary.boundaryPoint_boundary (k:=ℚ) e
    have hz : IsLocalRing.closedPoint ℚ ∉ boundaryPoint (k:=ℚ) e ⁻¹ᵁ ThetaBoundary.tOpen := by
      rw [hb];simp
    exact hz

theorem boundary_finite : ((tOpen (k:=ℚ) : Set (C ℚ))ᶜ).Finite := by
  rw [boundary_eq_range]
  exact Set.finite_range boundarySupport

theorem origin_mem_boundary :
    ThetaActualPoints.originC (k:=ℚ) (IsLocalRing.closedPoint ℚ) ∈ (tOpen (k:=ℚ) : Set (C ℚ))ᶜ := by
  rw [boundary_eq_range]
  exact ⟨fun _=>true,rfl⟩

end FourCorner.ThetaCSchemeBoundaryFinite
