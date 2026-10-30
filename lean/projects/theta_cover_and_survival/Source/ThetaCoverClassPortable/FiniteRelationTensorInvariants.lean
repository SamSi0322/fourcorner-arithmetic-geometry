import ThetaCoverClassPortable.FiniteRelationRationalTraceSplit

namespace FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u v
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]

 def baseChangedSource (s : A →+* B) (S : Type v) [CommRing S] [Algebra C S] :
    letI := relationAlgebra (C:=C) s; S ⊗[C] A →ₐ[S] S ⊗[C] B := by
  letI := relationAlgebra (C:=C) s
  exact Algebra.TensorProduct.map (AlgHom.id S S) (sourceAlg (C:=C) s)

 def baseChangedTarget (s t : A →+* B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (S : Type v) [CommRing S] [Algebra C S] :
    letI := relationAlgebra (C:=C) s; S ⊗[C] A →ₐ[S] S ⊗[C] B := by
  letI := relationAlgebra (C:=C) s
  exact Algebra.TensorProduct.map (AlgHom.id S S) (targetAlg s t hinv)

 theorem baseChanged_difference (s t : A →+* B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (S : Type v) [CommRing S] [Algebra C S] :
    letI := relationAlgebra (C:=C) s
    (baseChangedTarget s t hinv S).toLinearMap-(baseChangedSource (C:=C) s S).toLinearMap=
      (relationDifference s t hinv).baseChange S := by
  letI := relationAlgebra (C:=C) s
  rw [relationDifference,LinearMap.baseChange_sub]
  rfl

 theorem scalar_baseChange_inclusion (S : Type v) [CommRing S] [Algebra C S] :
    (Algebra.linearMap C A).baseChange S=
      (Algebra.linearMap S (S ⊗[C] A)).comp (Algebra.TensorProduct.rid C S S).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s c =>
      change s ⊗ₜ[C] algebraMap C A c=algebraMap S (S ⊗[C] A) (c • s)
      simp only [Algebra.TensorProduct.algebraMap_apply]
      change s ⊗ₜ[C] algebraMap C A c=(c • s) ⊗ₜ[C] (1 : A)
      calc
        s ⊗ₜ[C] algebraMap C A c=s ⊗ₜ[C] (c • (1 : A)) := by simp only [Algebra.smul_def,mul_one]
        _ = c • (s ⊗ₜ[C] (1 : A)) := TensorProduct.tmul_smul c s 1
        _ = (c • s) ⊗ₜ[C] (1 : A) := TensorProduct.smul_tmul' c s 1
  | add x y hx hy => simpa only [map_add] using congrArg₂ (·+·) hx hy

/-- Exact invariants of the ACTUAL native base-changed ring maps are
precisely the actual scalar image of S. No flatness of S/C is assumed. -/
theorem rational_constantRank_tensor_invariants [Algebra ℚ A] (s t : A →+* B)
    (hfinite : letI := s.toAlgebra;Module.Finite A B)
    (hprojective : letI := s.toAlgebra;Module.Projective A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0)
    (hrank : letI := s.toAlgebra;∀q : PrimeSpectrum A,Module.rankAtStalk B q=n)
    (S : Type v) [CommRing S] [Algebra C S] :
    letI := relationAlgebra (C:=C) s
    ∀x : S ⊗[C] A,baseChangedSource (C:=C) s S x=baseChangedTarget s t hinv S x ↔
      x∈Set.range (algebraMap S (S ⊗[C] A)) := by
  letI := relationAlgebra (C:=C) s
  have hker := rational_constantRank_baseChange_invariants s t hfinite hprojective hgen heq hinj hinv hbase n hn hrank S
  intro x
  have hx : baseChangedSource (C:=C) s S x=baseChangedTarget s t hinv S x ↔
      x∈LinearMap.ker ((relationDifference s t hinv).baseChange S) := by
    rw [← baseChanged_difference]
    change _ ↔ baseChangedTarget s t hinv S x-baseChangedSource (C:=C) s S x=0
    exact eq_comm.trans sub_eq_zero.symm
  rw [hx,← hker]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨Algebra.TensorProduct.rid C S S z,?_⟩
    rw [scalar_baseChange_inclusion] at hz
    exact hz
  · rintro ⟨z,rfl⟩
    refine ⟨(Algebra.TensorProduct.rid C S S).symm z,?_⟩
    rw [scalar_baseChange_inclusion]
    change algebraMap S (S ⊗[C] A) ((Algebra.TensorProduct.rid C S S) ((Algebra.TensorProduct.rid C S S).symm z))=_
    rw [AlgEquiv.apply_symm_apply]

/-- The scalar inclusion itself remains injective after every base
change, proved from the actual normalized-trace retraction. -/
theorem rational_constantRank_tensor_scalar_injective [Algebra ℚ A] (s t : A →+* B)
    (hfinite : letI := s.toAlgebra;Module.Finite A B)
    (hprojective : letI := s.toAlgebra;Module.Projective A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0)
    (hrank : letI := s.toAlgebra;∀q : PrimeSpectrum A,Module.rankAtStalk B q=n)
    (S : Type v) [CommRing S] [Algebra C S] :
    Function.Injective (algebraMap S (S ⊗[C] A)) := by
  obtain ⟨P,H,hret,-⟩ := rational_constantRank_split s t hfinite hprojective hgen heq hinj hinv hbase n hn hrank
  have hri := FourCorner.SplitLinearEqualizerBaseChange.baseChange_retraction (Algebra.linearMap C A) P hret S
  have hi : Function.Injective ((Algebra.linearMap C A).baseChange S) :=
    Function.LeftInverse.injective (fun z=>LinearMap.congr_fun hri z)
  intro x y hxy
  apply (Algebra.TensorProduct.rid C S S).symm.injective
  apply hi
  simp only [scalar_baseChange_inclusion,LinearMap.comp_apply]
  change algebraMap S (S ⊗[C] A) ((Algebra.TensorProduct.rid C S S) ((Algebra.TensorProduct.rid C S S).symm x))=
    algebraMap S (S ⊗[C] A) ((Algebra.TensorProduct.rid C S S) ((Algebra.TensorProduct.rid C S S).symm y))
  simpa only [AlgEquiv.apply_symm_apply] using hxy

#print axioms rational_constantRank_tensor_scalar_injective

#print axioms rational_constantRank_tensor_invariants
end
end FourCorner.FiniteRelationQuotient
