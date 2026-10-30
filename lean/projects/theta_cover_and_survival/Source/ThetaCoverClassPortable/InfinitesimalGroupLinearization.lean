import ThetaCoverClassPortable.InfinitesimalAffineChart
import ThetaCoverClassPortable.NaturalDerivationAddition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Infinitesimal
open Multiplication
variable (G : Over base) [GrpObj G]
variable (A : Type) [CommRing A] [Algebra ℚ A]
variable (j : pointObject A ⟶ G) [IsOpenImmersion j.left]
variable (ε : A →ₐ[ℚ] ℚ) (he : pointChange ε ≫ j=1)

def derivationMul (M : Type) [AddCommGroup M] [Module ℚ M]
    (d e : Augmented.augDeriv ε M) : Augmented.augDeriv ε M :=
  pointDerivEquiv G A j ε he
    ((pointDerivEquiv G A j ε he).symm d*(pointDerivEquiv G A j ε he).symm e)

variable {M N : Type} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

theorem pointDeriv_symm_natural (f : M →ₗ[ℚ] N) (d : Augmented.augDeriv ε M) :
    tangentMap G f ((pointDerivEquiv G A j ε he).symm d)=
      (pointDerivEquiv G A j ε he).symm (Augmented.push ε f d) := by
  apply (pointDerivEquiv G A j ε he).injective
  rw [pointDeriv_natural,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem derivationMul_natural (f : M →ₗ[ℚ] N) (d e : Augmented.augDeriv ε M) :
    Augmented.push ε f (derivationMul G A j ε he M d e)=
      derivationMul G A j ε he N (Augmented.push ε f d) (Augmented.push ε f e) := by
  unfold derivationMul
  rw [←pointDeriv_natural,map_mul,pointDeriv_symm_natural,pointDeriv_symm_natural]

theorem pointDeriv_symm_zero :
    (pointDerivEquiv G A j ε he).symm (0 : Augmented.augDeriv ε M)=1 := by
  apply (pointDerivEquiv G A j ε he).injective
  rw [Equiv.apply_symm_apply,pointDeriv_one]

theorem derivationMul_zero_left (M : Type) [AddCommGroup M] [Module ℚ M]
    (d : Augmented.augDeriv ε M) : derivationMul G A j ε he M 0 d=d := by
  unfold derivationMul
  rw [pointDeriv_symm_zero,one_mul,Equiv.apply_symm_apply]

theorem derivationMul_zero_right (M : Type) [AddCommGroup M] [Module ℚ M]
    (d : Augmented.augDeriv ε M) : derivationMul G A j ε he M d 0=d := by
  unfold derivationMul
  rw [pointDeriv_symm_zero,mul_one,Equiv.apply_symm_apply]

/-- Group multiplication on ACTUAL infinitesimal scheme points equals
addition of ACTUAL native derivations. It follows from naturality and
square-zero direct sums, without postulating a tangent group law. -/
theorem pointDeriv_mul (P Q : tangentPoints G M) :
    pointDerivEquiv G A j ε he (P*Q)=
      pointDerivEquiv G A j ε he P+pointDerivEquiv G A j ε he Q := by
  have h := Augmented.natural_operation_is_add ε (derivationMul G A j ε he)
    (fun M N _ _ _ _ f d e => derivationMul_natural G A j ε he f d e)
    (fun M _ _ d => derivationMul_zero_left G A j ε he M d)
    (fun M _ _ d => derivationMul_zero_right G A j ε he M d)
    M (pointDerivEquiv G A j ε he P) (pointDerivEquiv G A j ε he Q)
  simpa only [derivationMul,Equiv.symm_apply_apply] using h

/-- Exact additive equivalence for the genuine group kernel. -/
def pointDerivAddEquiv : Additive (tangentPoints G M) ≃+ Augmented.augDeriv ε M where
  toFun P := pointDerivEquiv G A j ε he P.toMul
  invFun d := Additive.ofMul ((pointDerivEquiv G A j ε he).symm d)
  left_inv P := congrArg Additive.ofMul ((pointDerivEquiv G A j ε he).symm_apply_apply P.toMul)
  right_inv d := (pointDerivEquiv G A j ε he).apply_symm_apply d
  map_add' P Q := pointDeriv_mul G A j ε he P.toMul Q.toMul

/-- The first-order action of actual [m] is scalar multiplication by m. -/
theorem pointDeriv_pow (P : tangentPoints G M) (m : ℕ) :
    pointDerivEquiv G A j ε he (P^m)=(m:ℚ) • pointDerivEquiv G A j ε he P := by
  induction m with
  | zero => simp only [pow_zero,pointDeriv_one,Nat.cast_zero,zero_smul]
  | succ m ih =>
    rw [pow_succ,pointDeriv_mul,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_smul,one_smul]

include ε he in
/-- Unique correction in the actual infinitesimal identity kernel. -/
theorem tangentPoints_unique_root (m : ℕ) (hm : 0<m) (P : tangentPoints G M) :
    ∃! Q : tangentPoints G M,Q^m=P := by
  have hmQ : (m:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  refine ⟨(pointDerivEquiv G A j ε he).symm ((m:ℚ)⁻¹ • pointDerivEquiv G A j ε he P),?_,?_⟩
  · apply (pointDerivEquiv G A j ε he).injective
    rw [pointDeriv_pow,Equiv.apply_symm_apply,smul_smul,mul_inv_cancel₀ hmQ,one_smul]
  · intro Q hQ
    apply (pointDerivEquiv G A j ε he).injective
    rw [Equiv.apply_symm_apply]
    have h := congrArg (pointDerivEquiv G A j ε he) hQ
    rw [pointDeriv_pow] at h
    calc
      pointDerivEquiv G A j ε he Q=(m:ℚ)⁻¹ • ((m:ℚ) • pointDerivEquiv G A j ε he Q) := by
        rw [smul_smul,inv_mul_cancel₀ hmQ,one_smul]
      _ = _ := by rw [h]

end FourCorner.ThetaLocalSurvival.Infinitesimal
