import ThetaCoverClassPortable.ReplayImports
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped TensorProduct
universe u
namespace FourCorner.PolynomialLevelFibre
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
/-- The polynomial module is genuinely finite free, by the PID theorem. -/
theorem finite_free_of_injective [IsDomain A] (f : A)
    (hinj : Function.Injective (Polynomial.aeval f : Polynomial K →ₐ[K] A))
    (hfinite : (Polynomial.aeval f : Polynomial K →ₐ[K] A).toRingHom.Finite) :
    letI := (Polynomial.aeval f : Polynomial K →ₐ[K] A).toRingHom.toAlgebra
    Module.Finite (Polynomial K) A ∧ Module.Free (Polynomial K) A := by
  letI := (Polynomial.aeval f : Polynomial K →ₐ[K] A).toRingHom.toAlgebra
  haveI : Module.Finite (Polynomial K) A := hfinite
  haveI : Module.IsTorsionFree (Polynomial K) A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  exact ⟨inferInstance, inferInstance⟩

section Equivalence
variable {S : Type u} [CommRing S] [Algebra K S]
variable [Algebra (Polynomial K) A] [IsScalarTower K (Polynomial K) A]
variable [Algebra (Polynomial K) S] [IsScalarTower K (Polynomial K) S]

/-- The equation cutting out a level fibre is precisely the polynomial balancing relation. -/
def relation : S ⊗[K] A :=
  (1 : S) ⊗ₜ[K] algebraMap (Polynomial K) A Polynomial.X -
    algebraMap (Polynomial K) S Polynomial.X ⊗ₜ[K] (1 : A)

def toBalanced : S ⊗[K] A →ₐ[S] S ⊗[Polynomial K] A :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (Algebra.TensorProduct.includeRight.restrictScalars K) (fun _ _ => .all _ _)

lemma toBalanced_relation : toBalanced (K := K) (A := A) (S := S) relation = 0 := by
  simp [relation, toBalanced, Algebra.TensorProduct.includeRight]

abbrev Fibre := (S ⊗[K] A) ⧸ Ideal.span {relation (K := K) (A := A) (S := S)}

set_option backward.isDefEq.respectTransparency false in
/-- Quotient presentation of polynomial base change, with no freeness hypothesis. -/
def quotientEquiv : Fibre (K := K) (A := A) (S := S) ≃ₐ[S] S ⊗[Polynomial K] A := by
  let I : Ideal (S ⊗[K] A) := Ideal.span {relation}
  let Q := (S ⊗[K] A) ⧸ I
  letI : Algebra (Polynomial K) Q := (algebraMap S Q).comp (algebraMap (Polynomial K) S) |>.toAlgebra
  letI : SMul (Polynomial K) Q := (inferInstance : Algebra (Polynomial K) Q).toSMul
  haveI : IsScalarTower (Polynomial K) S Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K (Polynomial K) Q := IsScalarTower.to₁₂₄ K (Polynomial K) S Q
  let q : S ⊗[K] A →ₐ[S] Q := Ideal.Quotient.mkₐ S I
  let rightK : A →ₐ[K] Q := (q.restrictScalars K).comp Algebra.TensorProduct.includeRight
  have hrel : q relation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hq (x : S) : q (x ⊗ₜ[K] (1 : A)) = algebraMap S Q x := q.commutes x
  have hx : rightK (algebraMap (Polynomial K) A Polynomial.X) =
      algebraMap (Polynomial K) Q Polynomial.X := by
    have hh := (map_sub q _ _).trans hrel
    exact sub_eq_zero.mp (by simpa [rightK, relation, Algebra.TensorProduct.includeRight, hq,
      IsScalarTower.algebraMap_eq (Polynomial K) S Q] using hh)
  have hc : rightK.toRingHom.comp (algebraMap (Polynomial K) A) = algebraMap (Polynomial K) Q := by
    have hh : rightK.comp (IsScalarTower.toAlgHom K (Polynomial K) A) =
        IsScalarTower.toAlgHom K (Polynomial K) Q := Polynomial.algHom_ext hx
    exact congrArg AlgHom.toRingHom hh
  let right : A →ₐ[Polynomial K] Q :=
    { rightK.toRingHom with commutes' := fun p => RingHom.congr_fun hc p }
  let back : S ⊗[Polynomial K] A →ₐ[S] Q :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) right (fun _ _ => .all _ _)
  have hker : ∀ a ∈ I, toBalanced (K := K) (A := A) (S := S) a = 0 := by
    intro a ha
    exact (show I ≤ RingHom.ker toBalanced from
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (show toBalanced relation = 0 from toBalanced_relation))) ha
  let forward : Q →ₐ[S] S ⊗[Polynomial K] A := Ideal.Quotient.liftₐ I toBalanced hker
  have hf (a : S ⊗[K] A) : forward (q a) = toBalanced a := by
    exact DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp I toBalanced hker) a
  have hb (a : S) (b : A) : back (a ⊗ₜ[Polynomial K] b) = algebraMap S Q a * right b := by
    exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
  exact AlgEquiv.ofAlgHom forward back (by
    ext x
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply]
    rw [hb]
    simp only [map_one, one_mul]
    change forward (q (1 ⊗ₜ[K] x)) = 1 ⊗ₜ[Polynomial K] x
    rw [hf]
    simp [toBalanced]) (by
    apply Ideal.Quotient.algHom_ext
    ext x
    change back (toBalanced (1 ⊗ₜ[K] x)) = q (1 ⊗ₜ[K] x)
    simp only [toBalanced, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    change back (1 ⊗ₜ[Polynomial K] x) = q (1 ⊗ₜ[K] x)
    simp only [back, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl)

/-- Finite free polynomial algebras have finite free level fibres of the same rank. -/
theorem fibre_finite_free [Nontrivial S] [Module.Finite (Polynomial K) A]
    [Module.Free (Polynomial K) A] :
    Module.Finite S (Fibre (K := K) (A := A) (S := S)) ∧
      Module.Free S (Fibre (K := K) (A := A) (S := S)) ∧
      Module.finrank S (Fibre (K := K) (A := A) (S := S)) = Module.finrank (Polynomial K) A := by
  let e := (quotientEquiv (K := K) (A := A) (S := S)).toLinearEquiv
  exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm,
    e.finrank_eq.trans Module.finrank_baseChange⟩

end Equivalence

/-- The exact quotient in `FiniteMapData.levelSet_free`, over every nonzero base algebra.
The only input is a finite injective polynomial map into a domain. -/
theorem all_levelSets_finite_free [IsDomain A] (f : A)
    (hinj : Function.Injective (Polynomial.aeval f : Polynomial K →ₐ[K] A))
    (hfinite : (Polynomial.aeval f : Polynomial K →ₐ[K] A).toRingHom.Finite)
    (S : Type u) [CommRing S] [Algebra K S] [Nontrivial S] (s : S) :
    letI := (Polynomial.aeval f : Polynomial K →ₐ[K] A).toRingHom.toAlgebra
    Module.Finite S ((S ⊗[K] A) ⧸ Ideal.span {(1 : S) ⊗ₜ[K] f - s ⊗ₜ[K] (1 : A)}) ∧
      Module.Free S ((S ⊗[K] A) ⧸ Ideal.span {(1 : S) ⊗ₜ[K] f - s ⊗ₜ[K] (1 : A)}) ∧
      Module.finrank S ((S ⊗[K] A) ⧸ Ideal.span {(1 : S) ⊗ₜ[K] f - s ⊗ₜ[K] (1 : A)}) =
        Module.finrank (Polynomial K) A := by
  letI := (Polynomial.aeval f : Polynomial K →ₐ[K] A).toRingHom.toAlgebra
  letI := (Polynomial.aeval s : Polynomial K →ₐ[K] S).toRingHom.toAlgebra
  haveI : IsScalarTower K (Polynomial K) A := IsScalarTower.of_algHom (Polynomial.aeval f)
  haveI : IsScalarTower K (Polynomial K) S := IsScalarTower.of_algHom (Polynomial.aeval s)
  haveI : Module.Finite (Polynomial K) A := (finite_free_of_injective f hinj hfinite).1
  haveI : Module.Free (Polynomial K) A := (finite_free_of_injective f hinj hfinite).2
  have hf : algebraMap (Polynomial K) A Polynomial.X = f := Polynomial.aeval_X f
  have hs : algebraMap (Polynomial K) S Polynomial.X = s := Polynomial.aeval_X s
  have h := fibre_finite_free (K := K) (A := A) (S := S)
  have he : Ideal.span {relation (K := K) (A := A) (S := S)} =
      Ideal.span {(1 : S) ⊗ₜ[K] f - s ⊗ₜ[K] (1 : A)} := by
    simp only [relation, hf, hs]
  let e := (Ideal.quotientEquivAlgOfEq S he).toLinearEquiv
  haveI : Module.Finite S (Fibre (K := K) (A := A) (S := S)) := h.1
  haveI : Module.Free S (Fibre (K := K) (A := A) (S := S)) := h.2.1
  exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e, e.finrank_eq.symm.trans h.2.2⟩

/-- The rank uses the specified, actual polynomial evaluation algebra structure. -/
def polynomialRank (f : A) : ℕ :=
  letI := (Polynomial.aeval f : Polynomial K →ₐ[K] A).toRingHom.toAlgebra
  Module.finrank (Polynomial K) A

/-- This has precisely the all-local-base quantifiers and quotient of `FiniteMapData`. -/
theorem local_levelSet_free [IsDomain A] (f : A)
    (hinj : Function.Injective (Polynomial.aeval f : Polynomial K →ₐ[K] A))
    (hfinite : (Polynomial.aeval f : Polynomial K →ₐ[K] A).toRingHom.Finite) :
    ∀ (S : Type u) [CommRing S] [Algebra K S] [IsLocalRing S] (s : S),
      Module.Finite S ((S ⊗[K] A) ⧸ Ideal.span {(1 : S) ⊗ₜ[K] f - s ⊗ₜ[K] (1 : A)}) ∧
        Module.Free S ((S ⊗[K] A) ⧸ Ideal.span {(1 : S) ⊗ₜ[K] f - s ⊗ₜ[K] (1 : A)}) ∧
        Module.finrank S ((S ⊗[K] A) ⧸ Ideal.span {(1 : S) ⊗ₜ[K] f - s ⊗ₜ[K] (1 : A)}) =
          polynomialRank (K := K) f := by
  intro S _ _ _ s
  exact all_levelSets_finite_free f hinj hfinite S s

end FourCorner.PolynomialLevelFibre
