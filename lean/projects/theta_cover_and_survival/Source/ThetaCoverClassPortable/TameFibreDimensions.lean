import ThetaCoverClassPortable.PointedFieldEffectivity
import ThetaCoverClassPortable.TameFibrePoint
import ThetaCoverClassPortable.FiniteRelationBaseChangeModules
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A] [Algebra ℚ A]

/-- COMPLETE dimension theorem for EVERY actual field scalar fibre of
the original tame relation. All relation/module/rank/invariant/point
premises of the fieldcase are DERIVED internally. No fibre dimension,
coassoc/effectivity, rational-point or model identity is assumed. -/
theorem tame_field_dimensions [Module.Finite C A] (s t : A →+* B)
    (hf : letI := s.toAlgebra;Module.Finite A B)
    (hp : letI := s.toAlgebra;Module.Projective A B)
    (ht : letI := t.toAlgebra;Module.Flat A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0) (hr : letI := s.toAlgebra;∀p : PrimeSpectrum A,Module.rankAtStalk B p=n)
    (K : Type u) [Field K] [Algebra C K] : Module.finrank K (K ⊗[C] A)=n := by
  obtain ⟨L,hField,hAlg,hFinite,x,hDim⟩ := tame_exists_finite_point s t hf hp hgen heq hinj hinv hbase n hn hr K
  letI := hField
  letI := hAlg
  letI := hFinite
  letI : Algebra C L := ((algebraMap K L).comp (algebraMap C K)).toAlgebra
  letI := relationAlgebra (C:=C) s
  let sC : A →ₐ[C] B := sourceAlg (C:=C) s
  let tC : A →ₐ[C] B := targetAlg s t hinv
  let sL := FourCorner.FiniteRelationRingBaseChange.changeMap (S:=L) sC
  let tL := FourCorner.FiniteRelationRingBaseChange.changeMap (S:=L) tC
  obtain ⟨hfL,hpL⟩ := FourCorner.FiniteRelationRingBaseChange.changeMap_finite_projective (S:=L) sC hf hp
  have htL : tL.toRingHom.Flat := FourCorner.FiniteRelationRingBaseChange.changeMap_flat (S:=L) tC ht
  have hgL : sL.toRingHom.range ⊔ tL.toRingHom.range=⊤ :=
    FourCorner.FiniteRelationRingBaseChange.joint_generation_change (S:=L) sC tC hgen
  have heL := FourCorner.FiniteRelationRingBaseChange.equivalence_change (S:=L) sC tC heq
  have hiL : ∀a,sL a=tL a ↔ a∈Set.range (algebraMap L (L ⊗[C] A)) := by
    intro a
    exact rational_constantRank_tensor_invariants s t hf hp hgen heq hinj hinv hbase n hn hr L a
  have hrL := FourCorner.FiniteRelationRingBaseChange.changeMap_constant_rank (S:=L) sC hf hp n hr
  have hdimL := FourCorner.FiniteRelationOrbit.pointed_field_dimension sL tL x hfL hpL htL hgL heL hiL n hrL
  exact hDim.symm.trans hdimL

/-- Exact native residue-field version for the global quotient leaf. -/
theorem tame_residue_field_dimensions [Module.Finite C A] (s t : A →+* B)
    (hf : letI := s.toAlgebra;Module.Finite A B)
    (hp : letI := s.toAlgebra;Module.Projective A B)
    (ht : letI := t.toAlgebra;Module.Flat A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0) (hr : letI := s.toAlgebra;∀p : PrimeSpectrum A,Module.rankAtStalk B p=n) :
    ∀p : PrimeSpectrum C,Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A)=n := by
  intro p
  exact tame_field_dimensions s t hf hp ht hgen heq hinj hinv hbase n hn hr p.asIdeal.ResidueField

#print axioms tame_field_dimensions
#print axioms tame_residue_field_dimensions
end
end FourCorner.FiniteRelationQuotient
