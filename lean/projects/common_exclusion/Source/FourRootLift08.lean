import geometry.MultiquadraticCoordinateUniversal
import CommonActualDegree
import CommonFieldCoordinates
noncomputable section
namespace FourCorner.FourRootLift08
open Polynomial
open Multiquadratic.CoordinateAlgebra
open Multiquadratic.CoordinateUniversal
variable (R : Type*) [CommRing R]
def equation (q : Fin 4 → R) : (Stage₃ R (q 0) (q 1) (q 2))[X] :=
  X^2-C (algebraMap R (Stage₃ R (q 0) (q 1) (q 2)) (q 3))
abbrev A (q : Fin 4 → R) := AdjoinRoot (equation R q)
theorem monic (q : Fin 4 → R) : (equation R q).Monic := monic_X_pow_sub_C _ (by decide)
def basis (q : Fin 4 → R) := (basis₃ R (q 0) (q 1) (q 2)).smulTower
  (AdjoinRoot.powerBasis' (monic R q)).basis
instance finite (q : Fin 4 → R) : Module.Finite R (A R q) := Module.Finite.of_basis (basis R q)
instance free (q : Fin 4 → R) : Module.Free R (A R q) := Module.Free.of_basis (basis R q)
theorem finrank [Nontrivial R] (q : Fin 4 → R) : Module.finrank R (A R q) = 16 := by
  rw [Module.finrank_eq_card_basis (basis R q)]
  simp only [Fintype.card_prod,Fintype.card_fin]
  change (equation₁ R (q 0)).natDegree * (equation₂ R (q 0) (q 1)).natDegree *
    (equation₃ R (q 0) (q 1) (q 2)).natDegree * (equation R q).natDegree = 16
  simp only [equation₁,equation₂,equation₃,equation,natDegree_X_pow_sub_C]

def coord (q : Fin 4 → R) : Fin 4 → A R q
  | 0 => algebraMap _ _ (coordinate₁ R (q 0) (q 1) (q 2))
  | 1 => algebraMap _ _ (coordinate₂ R (q 0) (q 1) (q 2))
  | 2 => algebraMap _ _ (coordinate₃ R (q 0) (q 1) (q 2))
  | 3 => AdjoinRoot.root (equation R q)
variable {S : Type*} [CommRing S]
def lift (i : R →+* S) (q : Fin 4 → R) (r : Fin 4 → S)
    (hr : ∀ k, r k ^ 2 = i (q k)) : A R q →+* S :=
  AdjoinRoot.lift (Multiquadratic.CoordinateUniversal.lift R S i (q 0) (q 1) (q 2)
    (r 0) (r 1) (r 2) (hr 0) (hr 1) (hr 2)) (r 3) (by
      simp only [equation,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,
        lift_algebraMap,hr,sub_self])
@[simp] theorem lift_algebraMap (i : R →+* S) (q : Fin 4 → R) (r : Fin 4 → S)
    (hr : ∀ k, r k ^ 2 = i (q k)) (x : R) :
    lift R i q r hr (algebraMap R (A R q) x) = i x := by
  rw [IsScalarTower.algebraMap_apply R (Stage₃ R (q 0) (q 1) (q 2)) (A R q)]
  exact (AdjoinRoot.lift_of _).trans (Multiquadratic.CoordinateUniversal.lift_algebraMap _ _ _ _ _ _ _ _ _ _ _ _ _)
@[simp] theorem lift_coord (i : R →+* S) (q : Fin 4 → R) (r : Fin 4 → S)
    (hr : ∀ k, r k ^ 2 = i (q k)) (k : Fin 4) :
    lift R i q r hr (coord R q k) = r k := by
  fin_cases k
  · exact (AdjoinRoot.lift_of _).trans (lift_coordinate₁ _ _ _ _ _ _ _ _ _ _ _ _)
  · exact (AdjoinRoot.lift_of _).trans (lift_coordinate₂ _ _ _ _ _ _ _ _ _ _ _ _)
  · exact (AdjoinRoot.lift_of _).trans (lift_coordinate₃ _ _ _ _ _ _ _ _ _ _ _ _)
  · exact AdjoinRoot.lift_root _

variable {F L : Type*} [Field F] [Field L] [Algebra F L]
def map (q : Fin 4 → F) (r : Fin 4 → L)
    (hr : ∀ k, r k ^ 2 = algebraMap F L (q k)) : A F q →ₐ[F] L where
  __ := lift F (algebraMap F L) q r hr
  commutes' := lift_algebraMap F (algebraMap F L) q r hr

def equiv (q : Fin 4 → F) (r : Fin 4 → L)
    (hr : ∀ k, r k ^ 2 = algebraMap F L (q k))
    (hg : Algebra.adjoin F (Set.range r) = ⊤)
    (hd : Module.finrank F L = 16) : A F q ≃ₐ[F] L := by
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

#print axioms equiv
end FourCorner.FourRootLift08
