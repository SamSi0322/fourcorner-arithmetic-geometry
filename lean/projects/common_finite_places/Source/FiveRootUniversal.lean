import FourRootLift08

noncomputable section
namespace FourCorner.FiveRootUniversal
open Polynomial
variable (R : Type*) [CommRing R]
abbrev firstFour (q : Fin 5 → R) : Fin 4 → R := fun i => q i.castSucc
abbrev B (q : Fin 5 → R) := FourRootLift08.A R (firstFour R q)
def equation (q : Fin 5 → R) : (B R q)[X] :=
  X^2-C (algebraMap R (B R q) (q 4))
abbrev A (q : Fin 5 → R) := AdjoinRoot (equation R q)
theorem monic (q : Fin 5 → R) : (equation R q).Monic := monic_X_pow_sub_C _ (by decide)
def basis (q : Fin 5 → R) := (FourRootLift08.basis R (firstFour R q)).smulTower
  (AdjoinRoot.powerBasis' (monic R q)).basis
instance finite (q : Fin 5 → R) : Module.Finite R (A R q) := Module.Finite.of_basis (basis R q)
instance free (q : Fin 5 → R) : Module.Free R (A R q) := Module.Free.of_basis (basis R q)
theorem finrank [Nontrivial R] (q : Fin 5 → R) : Module.finrank R (A R q) = 32 := by
  letI : Nontrivial (B R q) := Module.nontrivial_of_finrank_pos (R := R) (by
    change 0 < Module.finrank R (FourRootLift08.A R (firstFour R q))
    rw [FourRootLift08.finrank]; norm_num)
  rw [Module.finrank_eq_card_basis (basis R q)]
  simp only [Fintype.card_prod,Fintype.card_fin]
  change _ * (equation R q).natDegree = 32
  have h := FourRootLift08.finrank R (firstFour R q)
  rw [Module.finrank_eq_card_basis (FourRootLift08.basis R (firstFour R q))] at h
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  rw [h]
  rw [show (equation R q).natDegree = 2 from natDegree_X_pow_sub_C]

def coord (q : Fin 5 → R) : Fin 5 → A R q
  | 0 => algebraMap _ _ (FourRootLift08.coord R (firstFour R q) 0)
  | 1 => algebraMap _ _ (FourRootLift08.coord R (firstFour R q) 1)
  | 2 => algebraMap _ _ (FourRootLift08.coord R (firstFour R q) 2)
  | 3 => algebraMap _ _ (FourRootLift08.coord R (firstFour R q) 3)
  | 4 => AdjoinRoot.root (equation R q)
variable {S : Type*} [CommRing S]
def lift (i : R →+* S) (q : Fin 5 → R) (r : Fin 5 → S)
    (hr : ∀ k, r k ^ 2 = i (q k)) : A R q →+* S :=
  AdjoinRoot.lift (FourRootLift08.lift R i (firstFour R q) (fun j => r j.castSucc)
    (fun j => hr j.castSucc)) (r 4) (by
      simp only [equation,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C]
      change r 4 ^ 2 - FourRootLift08.lift R i (firstFour R q) (fun j => r j.castSucc)
        (fun j => hr j.castSucc) (algebraMap R (FourRootLift08.A R (firstFour R q)) (q 4)) = 0
      rw [hr,FourRootLift08.lift_algebraMap,sub_self])
@[simp] theorem lift_algebraMap (i : R →+* S) (q : Fin 5 → R) (r : Fin 5 → S)
    (hr : ∀ k, r k ^ 2 = i (q k)) (x : R) :
    lift R i q r hr (algebraMap R (A R q) x) = i x := by
  rw [IsScalarTower.algebraMap_apply R (B R q) (A R q)]
  exact (AdjoinRoot.lift_of _).trans (FourRootLift08.lift_algebraMap R i _ _ _ x)
@[simp] theorem lift_coord (i : R →+* S) (q : Fin 5 → R) (r : Fin 5 → S)
    (hr : ∀ k, r k ^ 2 = i (q k)) (k : Fin 5) :
    lift R i q r hr (coord R q k) = r k := by
  fin_cases k
  all_goals first
    | exact (AdjoinRoot.lift_of _).trans (FourRootLift08.lift_coord R i _ _ _ _)
    | exact AdjoinRoot.lift_root _

variable {F L : Type*} [Field F] [Field L] [Algebra F L]
def map (q : Fin 5 → F) (r : Fin 5 → L)
    (hr : ∀ k, r k ^ 2 = algebraMap F L (q k)) : A F q →ₐ[F] L where
  __ := lift F (algebraMap F L) q r hr
  commutes' := lift_algebraMap F (algebraMap F L) q r hr

def equiv (q : Fin 5 → F) (r : Fin 5 → L)
    (hr : ∀ k, r k ^ 2 = algebraMap F L (q k))
    (hg : Algebra.adjoin F (Set.range r) = ⊤)
    (hd : Module.finrank F L = 32) : A F q ≃ₐ[F] L := by
  letI : FiniteDimensional F L := Module.finite_of_finrank_pos (by rw [hd]; norm_num)
  let f := map q r hr
  have hs : Function.Surjective f := by
    have htop : f.range = ⊤ := by
      apply top_unique
      rw [← hg]
      apply Algebra.adjoin_le
      rintro _ ⟨k,rfl⟩
      exact ⟨coord F q k,lift_coord F (algebraMap F L) q r hr k⟩
    intro x
    have hx : x ∈ f.range := by rw [htop]; trivial
    exact hx
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank F q |>.trans hd.symm) (f := f.toLinearMap)).mpr hs
  exact AlgEquiv.ofBijective f ⟨hi,hs⟩

end FourCorner.FiveRootUniversal
#print axioms FourCorner.FiveRootUniversal.equiv
#print axioms FourCorner.FiveRootUniversal.lift_coord
