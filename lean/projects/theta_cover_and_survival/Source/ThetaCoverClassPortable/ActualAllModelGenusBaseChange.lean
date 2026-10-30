import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
universe u
namespace FourCorner.ActualPicardProperties

/-- Genus identification for every genuine geometric-fibre model, expressed
only through all-divisor RR. -/
def AllModelRRGenus {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) (g : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Spec (.of R))
    (F : Type u) [Field F] [Algebra k F] (M : CurveModel k F) (e : M.C ≅ pullback c s)
    (_ : e.hom ≫ pullback.snd c s=M.toBase) (Kc : Divisor k F) (g' : ℕ),
    (∀ D : Divisor k F, (ell D : ℤ)-ell (Kc-D)=Divisor.degree D+1-g') → g'=g

/-- The all-model RR genus identification is stable under actual base change;
the proof uses the true iterated pullback isomorphism. -/
theorem AllModelRRGenus.baseChange
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {g : ℕ}
    (hg : AllModelRRGenus c g) (T : Type u) [CommRing T] [Algebra R T] :
    AllModelRRGenus (SmoothProperCurve.baseChange R c T) g := by
  intro k _ _ s F _ _ M e he Kc g' hRR
  let i := pullbackLeftPullbackSndIso c (SmoothProperCurve.specMap R T) s
  let e' := e ≪≫ i
  have he' : e'.hom ≫ pullback.snd c (s ≫ SmoothProperCurve.specMap R T)=M.toBase := by
    change (e.hom ≫ i.hom) ≫ _ = _
    rw [Category.assoc,pullbackLeftPullbackSndIso_hom_snd]
    exact he
  exact hg k _ F M e' he' Kc g' hRR

/-- On an algebraically closed base field, the global all-fibre identification
also identifies RR for every actual model of the original curve. -/
theorem AllModelRRGenus.of_model
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {c : C ⟶ Spec (.of k)} {g : ℕ}
    (hg : AllModelRRGenus c g)
    {F : Type u} [Field F] [Algebra k F] (M : CurveModel k F) (e : M.C ≅ C)
    (he : e.hom ≫ c=M.toBase) (Kc : Divisor k F) (g' : ℕ)
    (hRR : ∀ D : Divisor k F, (ell D : ℤ)-ell (Kc-D)=Divisor.degree D+1-g') : g'=g := by
  let i : pullback c (𝟙 _) ≅ C := asIso (pullback.fst c (𝟙 _))
  have hi : i.inv ≫ pullback.snd c (𝟙 _) = c := by
    rw [Iso.inv_comp_eq]
    exact (pullback.condition.trans (Category.comp_id _)).symm
  exact hg k (𝟙 _) F M (e ≪≫ i.symm) (by simpa only [Iso.trans_hom,Iso.symm_hom,Category.assoc,hi] using he) Kc g' hRR

#print axioms AllModelRRGenus.baseChange
end FourCorner.ActualPicardProperties
