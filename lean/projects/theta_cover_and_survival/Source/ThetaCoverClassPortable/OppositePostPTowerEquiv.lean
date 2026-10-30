import ThetaCoverClassPortable.OppositePostPTower
import ThetaCoverClassPortable.OppositePostPSmooth

noncomputable section
namespace FourCorner.OppositeProjective.PostPTower
open Polynomial OppositePolynomials Multiquadratic.CoordinateUniversal
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1000000
abbrev ax (mu nu : K) (i : Fin 4) := PostPSmooth.ax mu nu i

lemma affineRelations (mu nu : K) :
    (ax mu nu 3)^2 = algebraMap K (PostPChart.affineRing mu nu) (A mu nu) -
      2*algebraMap K (PostPChart.affineRing mu nu) (A mu nu)*
        (algebraMap K (PostPChart.affineRing mu nu) nu)^2*(ax mu nu 0)^2 ∧
    (ax mu nu 1)^2 = 1+(algebraMap K (PostPChart.affineRing mu nu) mu)^2*(ax mu nu 0)^2+2*ax mu nu 3*ax mu nu 0 ∧
    (ax mu nu 2)^2 = 1+(algebraMap K (PostPChart.affineRing mu nu) mu)^2*(ax mu nu 0)^2-2*ax mu nu 3*ax mu nu 0 := by
  have he (i : Fin 3) : Ideal.Quotient.mk (PostPChart.affineIdeal mu nu) (PostPChart.affineEquation mu nu i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  have hc (c : K) : Ideal.Quotient.mk (PostPChart.affineIdeal mu nu) (MvPolynomial.C c) =
      algebraMap K (PostPChart.affineRing mu nu) c := rfl
  have h0 := he 0; have h1 := he 1; have h2 := he 2
  simp only [PostPChart.affineEquation,map_add,map_sub,map_pow,map_mul,map_one,hc,map_ofNat] at h0 h1 h2
  dsimp only [ax,PostPSmooth.ax]
  constructor
  · linear_combination h0
  constructor
  · linear_combination h1
  · linear_combination h2

lemma firstRootCondition (mu nu : K) :
    (ax mu nu 3)^2 = (aeval (ax mu nu 0)) (a mu nu) := by
  simpa [a,map_mul,map_pow,map_ofNat] using (affineRelations mu nu).1

def firstLift (mu nu : K) : First mu nu →+* PostPChart.affineRing mu nu :=
  lift₁ (Base K) (PostPChart.affineRing mu nu) (aeval (ax mu nu 0)).toRingHom
    (a mu nu) (ax mu nu 3) (firstRootCondition mu nu)
lemma firstLift_base (mu nu : K) (p : Base K) :
    firstLift mu nu (algebraMap (Base K) (First mu nu) p) = aeval (ax mu nu 0) p :=
  lift₁_algebraMap _ _ _ _ _ _ p
lemma firstLift_z (mu nu : K) : firstLift mu nu (z1 mu nu) = ax mu nu 3 :=
  lift₁_root _ _ _ _ _ _
lemma firstLift_t (mu nu : K) : firstLift mu nu (t1 mu nu) = ax mu nu 0 := by
  rw [t1,firstLift_base]; simp
lemma firstLift_constant (mu nu c : K) :
    firstLift mu nu (algebraMap K (First mu nu) c) = algebraMap K (PostPChart.affineRing mu nu) c := by
  rw [IsScalarTower.algebraMap_apply K (Base K) (First mu nu),firstLift_base]
  simp
lemma firstLift_b (mu nu : K) : firstLift mu nu (b mu nu) =
    1+(algebraMap K (PostPChart.affineRing mu nu) mu)^2*(ax mu nu 0)^2+2*ax mu nu 3*ax mu nu 0 := by
  simp [b,firstLift_constant,firstLift_z,firstLift_t,map_ofNat]
lemma firstLift_d (mu nu : K) : firstLift mu nu (d mu nu) =
    1+(algebraMap K (PostPChart.affineRing mu nu) mu)^2*(ax mu nu 0)^2-2*ax mu nu 3*ax mu nu 0 := by
  simp [d,firstLift_constant,firstLift_z,firstLift_t,map_ofNat]

def towerToAffine (mu nu : K) : Tower mu nu →+* PostPChart.affineRing mu nu :=
  Biquadratic.CoordinateAlgebra.lift (First mu nu) (PostPChart.affineRing mu nu)
    (firstLift mu nu) (b mu nu) (d mu nu) (ax mu nu 1) (ax mu nu 2)
    ((affineRelations mu nu).2.1.trans (firstLift_b mu nu).symm)
    ((affineRelations mu nu).2.2.trans (firstLift_d mu nu).symm)
lemma towerToAffine_first (mu nu : K) (x : First mu nu) :
    towerToAffine mu nu (algebraMap (First mu nu) (Tower mu nu) x) = firstLift mu nu x :=
  Biquadratic.CoordinateAlgebra.lift_algebraMap _ _ _ _ _ _ _ ((affineRelations mu nu).2.1.trans (firstLift_b mu nu).symm) ((affineRelations mu nu).2.2.trans (firstLift_d mu nu).symm) x
lemma towerToAffine_base (mu nu : K) (p : Base K) :
    towerToAffine mu nu (algebraMap (Base K) (Tower mu nu) p) = aeval (ax mu nu 0) p := by
  rw [IsScalarTower.algebraMap_apply (Base K) (First mu nu),towerToAffine_first,firstLift_base]
lemma towerToAffine_constant (mu nu c : K) :
    towerToAffine mu nu (algebraMap K (Tower mu nu) c) = algebraMap K (PostPChart.affineRing mu nu) c := by
  rw [IsScalarTower.algebraMap_apply K (First mu nu),towerToAffine_first,firstLift_constant]
lemma towerToAffine_t (mu nu : K) : towerToAffine mu nu (t mu nu) = ax mu nu 0 := by
  rw [t,towerToAffine_base]; simp
lemma towerToAffine_z (mu nu : K) : towerToAffine mu nu (z mu nu) = ax mu nu 3 := by
  rw [z,towerToAffine_first,firstLift_z]
lemma towerToAffine_q (mu nu : K) : towerToAffine mu nu (q mu nu) = ax mu nu 1 :=
  Biquadratic.CoordinateAlgebra.lift_coordinate₁ _ _ _ _ _ _ _ ((affineRelations mu nu).2.1.trans (firstLift_b mu nu).symm) ((affineRelations mu nu).2.2.trans (firstLift_d mu nu).symm)
lemma towerToAffine_r (mu nu : K) : towerToAffine mu nu (r mu nu) = ax mu nu 2 :=
  Biquadratic.CoordinateAlgebra.lift_coordinate₂ _ _ _ _ _ _ _ ((affineRelations mu nu).2.1.trans (firstLift_b mu nu).symm) ((affineRelations mu nu).2.2.trans (firstLift_d mu nu).symm)

def polyToTower (mu nu : K) : OppositeHomogeneousQuadrics.AffineAmbient K →+* Tower mu nu :=
  MvPolynomial.eval₂Hom (algebraMap K _) ![t mu nu,q mu nu,r mu nu,z mu nu]
lemma polyToTower_equation (mu nu : K) (i : Fin 3) :
    polyToTower mu nu (PostPChart.affineEquation mu nu i) = 0 := by
  obtain ⟨h0,h1,h2⟩ := originalRelations mu nu
  fin_cases i <;> simp only [polyToTower,MvPolynomial.coe_eval₂Hom,PostPChart.affineEquation,
    MvPolynomial.eval₂_sub,MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_C,MvPolynomial.eval₂_X,MvPolynomial.eval₂_one,MvPolynomial.eval₂_ofNat,map_one,map_mul,map_pow,map_ofNat,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  · linear_combination h0
  · linear_combination h1
  · linear_combination h2

def affineToTower (mu nu : K) : PostPChart.affineRing mu nu →+* Tower mu nu :=
  Ideal.Quotient.lift (PostPChart.affineIdeal mu nu) (polyToTower mu nu) (by
    have h : PostPChart.affineIdeal mu nu ≤ RingHom.ker (polyToTower mu nu) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact RingHom.mem_ker.mpr (polyToTower_equation mu nu i)
    exact fun a ha => h ha)
lemma affineToTower_ax (mu nu : K) (i : Fin 4) :
    affineToTower mu nu (ax mu nu i) = ![t mu nu,q mu nu,r mu nu,z mu nu] i := by
  change polyToTower mu nu (MvPolynomial.X i) = _
  simp [polyToTower]
lemma affineToTower_constant (mu nu c : K) :
    affineToTower mu nu (algebraMap K (PostPChart.affineRing mu nu) c) = algebraMap K (Tower mu nu) c := by
  change polyToTower mu nu (MvPolynomial.C c) = _
  simp [polyToTower]


lemma affineToTower_aeval (mu nu : K) (p : Base K) :
    affineToTower mu nu (aeval (ax mu nu 0) p) = algebraMap (Base K) (Tower mu nu) p := by
  have he : (affineToTower mu nu).comp (aeval (R := K) (ax mu nu 0)).toRingHom =
      algebraMap (Base K) (Tower mu nu) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      erw [Polynomial.aeval_C]
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K (Base K) (Tower mu nu)]
      exact affineToTower_constant mu nu c
    · simp only [RingHom.comp_apply]
      erw [Polynomial.aeval_X]
      exact affineToTower_ax mu nu 0
  exact RingHom.congr_fun he p

lemma first_inverse (mu nu : K) :
    (affineToTower mu nu).comp (firstLift mu nu) = algebraMap (First mu nu) (Tower mu nu) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro p
    change affineToTower mu nu (firstLift mu nu (algebraMap (Base K) (First mu nu) p)) =
      algebraMap (First mu nu) (Tower mu nu) (algebraMap (Base K) (First mu nu) p)
    rw [firstLift_base,affineToTower_aeval,← IsScalarTower.algebraMap_apply]
  · change affineToTower mu nu (firstLift mu nu (z1 mu nu)) = z mu nu
    rw [firstLift_z,affineToTower_ax]; rfl

lemma affine_tower_inverse (mu nu : K) :
    (towerToAffine mu nu).comp (affineToTower mu nu) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change towerToAffine mu nu (affineToTower mu nu (algebraMap K _ c)) = algebraMap K _ c
    rw [affineToTower_constant,towerToAffine_constant]
  · intro i
    change towerToAffine mu nu (affineToTower mu nu (ax mu nu i)) = ax mu nu i
    rw [affineToTower_ax]
    fin_cases i
    · exact towerToAffine_t mu nu
    · exact towerToAffine_q mu nu
    · exact towerToAffine_r mu nu
    · exact towerToAffine_z mu nu

lemma tower_affine_inverse (mu nu : K) :
    (affineToTower mu nu).comp (towerToAffine mu nu) = RingHom.id _ := by
  apply Biquadratic.CoordinateAlgebra.ringHom_ext
  · intro x
    change affineToTower mu nu (towerToAffine mu nu (algebraMap (First mu nu) (Tower mu nu) x)) =
      algebraMap (First mu nu) (Tower mu nu) x
    rw [towerToAffine_first]
    exact RingHom.congr_fun (first_inverse mu nu) x
  · change affineToTower mu nu (towerToAffine mu nu (q mu nu)) = q mu nu
    rw [towerToAffine_q,affineToTower_ax]; rfl
  · change affineToTower mu nu (towerToAffine mu nu (r mu nu)) = r mu nu
    rw [towerToAffine_r,affineToTower_ax]; rfl

/-- Actual P-chart affine polynomial quotient equals the dependent monic tower. -/
def affineEquiv (mu nu : K) : PostPChart.affineRing mu nu ≃+* Tower mu nu :=
  RingEquiv.ofRingHom (affineToTower mu nu) (towerToAffine mu nu)
    (tower_affine_inverse mu nu) (affine_tower_inverse mu nu)

/-- The true boundary coordinate T/P in the P=1 affine presentation is regular. -/
theorem affine_t_regular (mu nu : K) : IsRegular (ax mu nu 0) := by
  have hr := t_regular mu nu
  have he : affineEquiv mu nu (ax mu nu 0) = t mu nu := affineToTower_ax mu nu 0
  have hinj : Function.Injective (fun x : PostPChart.affineRing mu nu => ax mu nu 0*x) := by
    intro x y hxy
    apply (affineEquiv mu nu).injective
    apply hr.left
    change t mu nu*(affineEquiv mu nu) x = t mu nu*(affineEquiv mu nu) y
    rw [← he, ← map_mul, ← map_mul]
    exact congrArg (affineEquiv mu nu) hxy
  exact ⟨hinj, fun x y hxy => hinj (by simpa only [mul_comm] using hxy)⟩

end FourCorner.OppositeProjective.PostPTower
#print axioms FourCorner.OppositeProjective.PostPTower.towerToAffine
#print axioms FourCorner.OppositeProjective.PostPTower.affineToTower

#print axioms FourCorner.OppositeProjective.PostPTower.affineEquiv
#print axioms FourCorner.OppositeProjective.PostPTower.affine_t_regular
