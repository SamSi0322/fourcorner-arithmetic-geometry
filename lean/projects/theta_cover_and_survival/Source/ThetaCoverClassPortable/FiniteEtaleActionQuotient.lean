import ThetaCoverClassPortable.InvariantOpenDescentAction
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.FiniteEtaleActionQuotient
open AffineDescentCoaction
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Algebra.Etale R S] [Module.FaithfullyFlat R S]
  {X : Scheme.{u}} (x:X⟶Spec (.of S)) (𝒜:DescentAction (s R S) x)

/-- The constructed affine quotient of a true invariant open has exactly the
restricted relation maps required by the genuine global quotient gluing. -/
lemma local_quotient (W:X.Opens) (hW:IsAffineOpen W)
    (hinv:pullback.fst (x≫s R S) (s R S) ⁻¹ᵁ W=𝒜.act ⁻¹ᵁ W) :
    ∃ (Y:Scheme.{u}) (p:W.toScheme⟶Y),
      (pullback.fst (x≫s R S) (s R S) ∣_ W)≫p=
        (((pullback (x≫s R S) (s R S)).isoOfEq hinv).hom≫(𝒜.act ∣_ W))≫p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (pullback.fst (x≫s R S) (s R S) ∣_ W)
        (((pullback (x≫s R S) (s R S)).isoOfEq hinv).hom≫(𝒜.act ∣_ W)) p p := by
  haveI : IsAffine W.toScheme := hW
  obtain ⟨Y,hY,p,w,hfin,hflat,hlfp,hsurj,hrel,hco⟩ :=
    GeneralAffineDescentQuotient.exists_quotient R S (W.ι≫x)
      (InvariantOpenDescentAction.action (s R S) x 𝒜 W hinv)
  have hk : IsPullback (pullback.fst (x≫s R S) (s R S) ∣_ W)
      (InvariantOpenDescentAction.tRes (s R S) x 𝒜 W hinv) p p := by
    refine hrel.of_iso (InvariantOpenDescentAction.relationIso (s R S) x W)
      (Iso.refl W.toScheme) (Iso.refl W.toScheme) (Iso.refl Y) ?_ ?_ ?_ ?_
    · simpa only [Iso.refl_hom,Category.comp_id] using
        (InvariantOpenDescentAction.relationIso_fst (s R S) x W).symm
    · simpa only [Iso.refl_hom,Category.comp_id] using
        (InvariantOpenDescentAction.relationIso_act (s R S) x 𝒜 W hinv).symm
    · simp
    · simp
  exact ⟨Y,p,hk.w,hfin,hflat,hlfp,hsurj,hk⟩

/-- Scheme effectivity of the actual known-base finite-etale action relation.
AF supplies actual invariant affine neighborhoods; each local quotient is
CONSTRUCTED by algebra coaction descent, then globally glued. -/
theorem exists_quotient
    (haff:∀ F:Finset X,∃U:X.Opens,IsAffineOpen U ∧ ∀z∈F,z∈U) :
    ∃ (Y:Scheme.{u}) (p:X⟶Y)
      (w:pullback.fst (x≫s R S) (s R S)≫p=𝒜.act≫p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (pullback.fst (x≫s R S) (s R S)) 𝒜.act p p ∧
      Nonempty (IsColimit (Cofork.ofπ p w)) := by
  have hsff:(algebraMap R S).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  haveI : Flat (s R S) := ((flat_and_surjective_SpecMap_iff _).mpr hsff).1
  haveI : IsFinite (s R S) := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : LocallyOfFinitePresentation (s R S) :=
    (HasRingHomProperty.Spec_iff (P:=@LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  haveI : IsFinite (pullback.fst (x≫s R S) (s R S)) := inferInstance
  haveI : Flat (pullback.fst (x≫s R S) (s R S)) := inferInstance
  haveI : LocallyOfFinitePresentation (pullback.fst (x≫s R S) (s R S)) := inferInstance
  haveI : IsFinite 𝒜.act := by rw [𝒜.act_eq_invol_fst];infer_instance
  haveI : Flat 𝒜.act := by rw [𝒜.act_eq_invol_fst];infer_instance
  haveI : LocallyOfFinitePresentation 𝒜.act := by rw [𝒜.act_eq_invol_fst];infer_instance
  have horbit : ∀z:X,∃U:X.Opens,IsAffineOpen U ∧
      ∀a:↥(pullback (C:=Scheme) (x≫s R S) (s R S)),pullback.fst (x≫s R S) (s R S) a=z → 𝒜.act a∈U := by
    intro z
    have hf := (pullback.fst (x≫s R S) (s R S)).finite_preimage_singleton z
    obtain ⟨U,hU,hFU⟩ := haff ((hf.image fun a=>𝒜.act a).toFinset)
    exact ⟨U,hU,fun a ha=>hFU _ (by rw [Set.Finite.mem_toFinset];exact ⟨a,by simpa using ha,rfl⟩)⟩
  choose U hU hOrbit using horbit
  choose W hW hxW _ hInv using fun z=>
    Scheme.exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst (x≫s R S) (s R S)) 𝒜.act (fun T=>𝒜.equivalence T) (hU z) (hOrbit z)
  exact Scheme.exists_quotient_of_forall_exists_quotient_restrict
    (pullback.fst (x≫s R S) (s R S)) 𝒜.act W hxW hInv
    (fun z=>local_quotient R S x 𝒜 (W z) (hW z) (hInv z))
end FourCorner.FiniteEtaleActionQuotient
