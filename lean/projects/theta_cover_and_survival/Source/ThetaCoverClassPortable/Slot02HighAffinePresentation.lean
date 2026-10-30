import ThetaCoverClassPortable.Slot02HighSchemeChart
import ThetaCoverClassPortable.geometry.OppositeAffineModel

noncomputable section
open AlgebraicGeometry MvPolynomial
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace FourCorner.OppositeProjective.HighAffine
open OppositeAffineModel OppositeCoordinateAlgebra OppositePolynomials
universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev ax (mu nu : K) (i : Fin 4) := Ideal.Quotient.mk (affineIdeal mu nu) (X i)
instance (mu nu : K) : Algebra K (affineRing mu nu) := Ideal.Quotient.algebra K

lemma affineRelations (mu nu : K) :
    (ax mu nu 3)^2 = algebraMap K (affineRing mu nu) (A mu nu) *
      ((ax mu nu 0)^2 - 2*(algebraMap K (affineRing mu nu) nu)^2) ∧
    (ax mu nu 1)^2 = (ax mu nu 0)^2 + (algebraMap K (affineRing mu nu) mu)^2 + 2*ax mu nu 3 ∧
    (ax mu nu 2)^2 = (ax mu nu 0)^2 + (algebraMap K (affineRing mu nu) mu)^2 - 2*ax mu nu 3 := by
  have h (i : Fin 3) : Ideal.Quotient.mk (affineIdeal mu nu)
      (OppositeHomogeneousQuadrics.affineEquation mu nu i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  simp only [OppositeHomogeneousQuadrics.affineEquation, map_sub, map_add, map_mul, map_pow] at h0 h1 h2
  have hc (a : K) : Ideal.Quotient.mk (affineIdeal mu nu) (C a) = algebraMap K (affineRing mu nu) a := rfl
  simp only [hc, map_ofNat] at h0 h1 h2
  dsimp only [ax]
  constructor
  · linear_combination h0
  constructor
  · linear_combination h1
  · linear_combination h2

def towerToAffine (mu nu : K) (hA : A mu nu ≠ 0) : ring mu nu →+* affineRing mu nu :=
  (existsUnique_original_lift mu nu hA (ax mu nu 3) (ax mu nu 0) (ax mu nu 1) (ax mu nu 2)
    (affineRelations mu nu)).choose

lemma towerToAffine_base (mu nu : K) (hA : A mu nu ≠ 0) (p : Polynomial K) :
    towerToAffine mu nu hA (algebraMap (Polynomial K) (ring mu nu) p) = Polynomial.aeval (ax mu nu 3) p :=
  (existsUnique_original_lift mu nu hA (ax mu nu 3) (ax mu nu 0) (ax mu nu 1) (ax mu nu 2)
    (affineRelations mu nu)).choose_spec.1.1 p
lemma towerToAffine_P (mu nu : K) (hA : A mu nu ≠ 0) :
    towerToAffine mu nu hA (coordinateP mu nu) = ax mu nu 0 :=
  (existsUnique_original_lift mu nu hA (ax mu nu 3) (ax mu nu 0) (ax mu nu 1) (ax mu nu 2)
    (affineRelations mu nu)).choose_spec.1.2.1
lemma towerToAffine_Q (mu nu : K) (hA : A mu nu ≠ 0) :
    towerToAffine mu nu hA (coordinateQ mu nu) = ax mu nu 1 :=
  (existsUnique_original_lift mu nu hA (ax mu nu 3) (ax mu nu 0) (ax mu nu 1) (ax mu nu 2)
    (affineRelations mu nu)).choose_spec.1.2.2.1
lemma towerToAffine_R (mu nu : K) (hA : A mu nu ≠ 0) :
    towerToAffine mu nu hA (coordinateR mu nu) = ax mu nu 2 :=
  (existsUnique_original_lift mu nu hA (ax mu nu 3) (ax mu nu 0) (ax mu nu 1) (ax mu nu 2)
    (affineRelations mu nu)).choose_spec.1.2.2.2

abbrev towerZ (mu nu : K) := algebraMap (Polynomial K) (ring mu nu) Polynomial.X

def polyToTower (mu nu : K) : OppositeHomogeneousQuadrics.AffineAmbient K →+* ring mu nu :=
  eval₂Hom (algebraMap K _) ![coordinateP mu nu,coordinateQ mu nu,coordinateR mu nu,towerZ mu nu]

lemma towerRelations (mu nu : K) (hA : A mu nu ≠ 0) :
    (towerZ mu nu)^2 = algebraMap K (ring mu nu) (A mu nu) *
      ((coordinateP mu nu)^2 - 2*(algebraMap K (ring mu nu) nu)^2) ∧
    (coordinateQ mu nu)^2 = (coordinateP mu nu)^2 + (algebraMap K (ring mu nu) mu)^2 + 2*towerZ mu nu ∧
    (coordinateR mu nu)^2 = (coordinateP mu nu)^2 + (algebraMap K (ring mu nu) mu)^2 - 2*towerZ mu nu := by
  have he : (Polynomial.aeval (towerZ mu nu) : Polynomial K →ₐ[K] ring mu nu) =
      IsScalarTower.toAlgHom K (Polynomial K) (ring mu nu) := by
    apply Polynomial.algHom_ext
    simp [towerZ]
  exact original_equations_of_hom mu nu hA (towerZ mu nu) (RingHom.id _) (by
    intro p; rw [he]; rfl)

lemma polyToTower_equation (mu nu : K) (hA : A mu nu ≠ 0) (i : Fin 3) :
    polyToTower mu nu (OppositeHomogeneousQuadrics.affineEquation mu nu i) = 0 := by
  obtain ⟨h0,h1,h2⟩ := towerRelations mu nu hA
  fin_cases i <;> simp only [polyToTower, coe_eval₂Hom, OppositeHomogeneousQuadrics.affineEquation,
    eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, eval₂_ofNat, map_ofNat, map_pow, map_mul]
  · linear_combination h0
  · linear_combination h1
  · linear_combination h2

def affineToTower (mu nu : K) (hA : A mu nu ≠ 0) : affineRing mu nu →+* ring mu nu :=
  Ideal.Quotient.lift (affineIdeal mu nu) (polyToTower mu nu) (by
    have h : affineIdeal mu nu ≤ RingHom.ker (polyToTower mu nu) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact RingHom.mem_ker.mpr (polyToTower_equation mu nu hA i)
    exact fun a ha => h ha)

lemma affineToTower_ax (mu nu : K) (hA : A mu nu ≠ 0) (i : Fin 4) :
    affineToTower mu nu hA (ax mu nu i) =
      ![coordinateP mu nu,coordinateQ mu nu,coordinateR mu nu,towerZ mu nu] i := by
  change polyToTower mu nu (X i) = _
  simp [polyToTower]

lemma affineToTower_constant (mu nu : K) (hA : A mu nu ≠ 0) (a : K) :
    affineToTower mu nu hA (algebraMap K _ a) = algebraMap K _ a := by
  change polyToTower mu nu (C a) = _
  simp [polyToTower]

lemma towerToAffine_constant (mu nu : K) (hA : A mu nu ≠ 0) (a : K) :
    towerToAffine mu nu hA (algebraMap K _ a) = algebraMap K _ a := by
  rw [IsScalarTower.algebraMap_apply K (Polynomial K) (ring mu nu), towerToAffine_base]
  simp

lemma affine_tower_inverse (mu nu : K) (hA : A mu nu ≠ 0) :
    (towerToAffine mu nu hA).comp (affineToTower mu nu hA) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change towerToAffine mu nu hA (affineToTower mu nu hA (algebraMap K _ a)) = algebraMap K _ a
    rw [affineToTower_constant, towerToAffine_constant]
  · intro i
    change towerToAffine mu nu hA (affineToTower mu nu hA (ax mu nu i)) = ax mu nu i
    rw [affineToTower_ax]
    fin_cases i
    · exact towerToAffine_P mu nu hA
    · exact towerToAffine_Q mu nu hA
    · exact towerToAffine_R mu nu hA
    · exact (towerToAffine_base mu nu hA Polynomial.X).trans (by simp)

lemma tower_affine_inverse (mu nu : K) (hA : A mu nu ≠ 0) :
    (affineToTower mu nu hA).comp (towerToAffine mu nu hA) = RingHom.id _ := by
  apply Multiquadratic.CoordinateUniversal.ringHom_ext
  · intro p
    change affineToTower mu nu hA (towerToAffine mu nu hA (algebraMap (Polynomial K) _ p)) = algebraMap (Polynomial K) _ p
    rw [towerToAffine_base]
    have he : (affineToTower mu nu hA).comp (Polynomial.aeval (R := K) (ax mu nu 3)).toRingHom =
        algebraMap (Polynomial K) (ring mu nu) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply]
        erw [Polynomial.aeval_C]
        rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K (Polynomial K) (ring mu nu)]
        exact affineToTower_constant mu nu hA a
      · simp only [RingHom.comp_apply]
        erw [Polynomial.aeval_X]
        exact affineToTower_ax mu nu hA 3
    exact RingHom.congr_fun he p
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [towerToAffine_P, affineToTower_ax]; rfl
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [towerToAffine_Q, affineToTower_ax]; rfl
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [towerToAffine_R, affineToTower_ax]; rfl

/-- Ring equivalence between the literal polynomial quotient and successive monic radical quotients. -/
def affineEquiv (mu nu : K) (hA : A mu nu ≠ 0) : affineRing mu nu ≃+* ring mu nu :=
  RingEquiv.ofRingHom (affineToTower mu nu hA) (towerToAffine mu nu hA)
    (tower_affine_inverse mu nu hA) (affine_tower_inverse mu nu hA)

end FourCorner.OppositeProjective.HighAffine
#print axioms FourCorner.OppositeProjective.HighAffine.affineEquiv
