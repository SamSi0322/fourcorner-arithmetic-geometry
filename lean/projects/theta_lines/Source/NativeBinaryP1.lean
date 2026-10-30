import BinaryDehomogenization
import Mathlib.LinearAlgebra.Projectivization.Basic

noncomputable section
set_option autoImplicit false
namespace FourCorner.BinaryQuarticDoubleRoots
variable {K : Type*} [Field K]
abbrev P1 (K : Type*) [Field K] := Projectivization K (Fin 2 → K)

theorem finite_vector_ne_zero (u : K) : (![u, 1] : Fin 2 → K) ≠ 0 := by
  intro h
  have hh := congrFun h 1
  simpa using hh

theorem infinity_vector_ne_zero : (![1, 0] : Fin 2 → K) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simpa using hh

def finitePoint (u : K) : P1 K := Projectivization.mk K ![u, 1] (finite_vector_ne_zero u)
def infinity : P1 K := Projectivization.mk K ![1, 0] infinity_vector_ne_zero

/-- Every actual native projective point is in the finite chart or is the genuine infinity. -/
theorem point_charts (P : P1 K) : P = infinity ∨ ∃ u : K, P = finitePoint u := by
  let v := P.rep
  have hv : v ≠ 0 := P.rep_nonzero
  have hp : Projectivization.mk K v hv = P := P.mk_rep
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      funext i
      fin_cases i <;> simp_all
    left
    rw [← hp]
    apply (Projectivization.mk_eq_mk_iff' K v ![1, 0] hv infinity_vector_ne_zero).mpr
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, h1]
  · right
    refine ⟨v 0 / v 1, ?_⟩
    rw [← hp]
    apply (Projectivization.mk_eq_mk_iff' K v ![v 0 / v 1, 1] hv (finite_vector_ne_zero _)).mpr
    refine ⟨v 1, ?_⟩
    funext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
    field_simp

theorem finitePoint_injective : Function.Injective (finitePoint : K → P1 K) := by
  intro u v h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hc1 : c = 1 := by simpa [Pi.smul_apply, smul_eq_mul] using congrFun hc 1
  have hc0 := congrFun hc 0
  simpa [Pi.smul_apply, smul_eq_mul, hc1] using hc0.symm

theorem infinity_ne_finite (u : K) : (infinity : P1 K) ≠ finitePoint u := by
  intro h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hc1 : c = 0 := by simpa [Pi.smul_apply, smul_eq_mul] using congrFun hc 1
  have hc0 := congrFun hc 0
  simpa [Pi.smul_apply, smul_eq_mul, hc1] using hc0

/-- The genuine zero locus of F in actual native projective space. -/
def ZeroAt (F : Binary K) (P : P1 K) : Prop :=
  ∃ (v : Fin 2 → K) (hv : v ≠ 0), P = Projectivization.mk K v hv ∧
    MvPolynomial.aeval v F = 0

theorem zeroAt_mk_iff {F : Binary K} {n : ℕ} (hF : F.IsHomogeneous n)
    (v : Fin 2 → K) (hv : v ≠ 0) :
    ZeroAt F (Projectivization.mk K v hv) ↔ MvPolynomial.aeval v F = 0 := by
  constructor
  · rintro ⟨w, hw, he, hz⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp he
    rw [← hc]
    change MvPolynomial.aeval ((c : K) • w) F = 0
    rw [eval_scale hF, hz, mul_zero]
  · intro hz
    exact ⟨v, hv, rfl, hz⟩

theorem zeroAt_finite_iff {F : Binary K} {n : ℕ} (hF : F.IsHomogeneous n) (u : K) :
    ZeroAt F (finitePoint u) ↔ MvPolynomial.aeval ![u, 1] F = 0 :=
  zeroAt_mk_iff hF _ (finite_vector_ne_zero u)

theorem zeroAt_infinity_iff {F : Binary K} {n : ℕ} (hF : F.IsHomogeneous n) :
    ZeroAt F infinity ↔ MvPolynomial.aeval (![1, 0] : Fin 2 → K) F = 0 :=
  zeroAt_mk_iff hF _ infinity_vector_ne_zero

/-- Values and BOTH actual formal partial derivatives at a representative. -/
def ZeroJet (F : Binary K) (v : Fin 2 → K) : Prop :=
  MvPolynomial.aeval v F = 0 ∧ ∀ i : Fin 2, MvPolynomial.aeval v (MvPolynomial.pderiv i F) = 0

/-- The actual native projective double-root condition, independent of any chosen chart. -/
def DoubleAt (F : Binary K) (P : P1 K) : Prop :=
  ∃ (v : Fin 2 → K) (hv : v ≠ 0), P = Projectivization.mk K v hv ∧ ZeroJet F v

/-- All nonzero scalar representatives have the same formal vanishing condition. -/
theorem zeroJet_scale {F : Binary K} (hF : F.IsHomogeneous 4)
    (a : K) (ha : a ≠ 0) (v : Fin 2 → K) : ZeroJet F (a • v) ↔ ZeroJet F v := by
  constructor
  · rintro ⟨h, hd⟩
    refine ⟨?_, ?_⟩
    · have he : a^4 * MvPolynomial.aeval v F = 0 := (eval_scale hF a v).symm.trans h
      exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ ha)
    · intro i
      have hi : (MvPolynomial.pderiv i F).IsHomogeneous 3 := hF.pderiv
      have he : a^3 * MvPolynomial.aeval v (MvPolynomial.pderiv i F) = 0 :=
        (eval_scale hi a v).symm.trans (hd i)
      exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ ha)
  · rintro ⟨h, hd⟩
    refine ⟨?_, ?_⟩
    · rw [eval_scale hF, h, mul_zero]
    · intro i
      have hi : (MvPolynomial.pderiv i F).IsHomogeneous 3 := hF.pderiv
      rw [eval_scale hi, hd i, mul_zero]

/-- Any nonzero representative of the actual native point may be used, not just the
existential representative from DoubleAt. -/
theorem doubleAt_mk_iff {F : Binary K} (hF : F.IsHomogeneous 4)
    (v : Fin 2 → K) (hv : v ≠ 0) :
    DoubleAt F (Projectivization.mk K v hv) ↔ ZeroJet F v := by
  constructor
  · rintro ⟨w, hw, he, hz⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp he
    rw [← hc]
    simpa only [Units.smul_def] using (zeroJet_scale hF (c : K) c.ne_zero w).mpr hz
  · intro hz
    exact ⟨v, hv, rfl, hz⟩

theorem doubleAt_finite_iff {F : Binary K} (hF : F.IsHomogeneous 4) (u : K) :
    DoubleAt F (finitePoint u) ↔ ZeroJet F ![u, 1] :=
  doubleAt_mk_iff hF _ (finite_vector_ne_zero u)

theorem doubleAt_infinity_iff {F : Binary K} (hF : F.IsHomogeneous 4) :
    DoubleAt F infinity ↔ ZeroJet F ![1, 0] :=
  doubleAt_mk_iff hF _ infinity_vector_ne_zero

end FourCorner.BinaryQuarticDoubleRoots
