import EllipticCurves.WeierstrassFormalGroup.Filtration
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-! The parameter modulo four on an actual deep elliptic-curve filtration.
The additivity is derived from the proved addition-series estimate, not supplied as a hypothesis.
No formal-logarithm identification is claimed in this file. -/
namespace FourCorner.CommonSource.Dyadic

open IsDedekindDomain IsLocalRing WeierstrassCurve.Affine

section FormalParameter
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
  {W : WeierstrassCurve.Affine (v.adicCompletion K)} [W.IsElliptic]
  [DecidableEq (v.adicCompletion K)] [CharZero K]
  (hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)

/-- The actual parameter-to-point equivalence, with its coordinate formula retained. -/
noncomputable def formalParameterEquiv : W₀.formalGroupLaw.Points ≃+ filtration hW 0 := by
  let f : W₀.formalGroupLaw.Points →+ filtration hW 0 :=
    { toFun := fun z => ⟨formalPoint hW z,
        (mem_pow_iff_formalPoint_mem_filtration z 0).mp (by simpa using (z ()).2)⟩
      map_zero' := Subtype.ext (formalPoint_of_param_eq_zero hW (z := 0) (by simp))
      map_add' := fun z z' => Subtype.ext (formalPoint_add hW z z') }
  exact AddEquiv.ofBijective f
    ⟨fun z z' h => formalPoint_injective hW (congrArg Subtype.val h), fun P => by
      obtain ⟨z, hz⟩ := formalPoint_surjective P.2
      exact ⟨z, Subtype.ext hz⟩⟩

@[simp] theorem formalParameterEquiv_coe (z : W₀.formalGroupLaw.Points) :
    ((formalParameterEquiv hW z : filtration hW 0) : W.Point) = formalPoint hW z := rfl

/-- Parameter of a point in `E_{k+1}`, regarded as a formal-group point. -/
noncomputable def formalParameter {k : ℕ} (P : filtration hW k) : W₀.formalGroupLaw.Points :=
  (formalParameterEquiv hW).symm (AddSubgroup.inclusion (filtration_anti (Nat.zero_le k)) P)

@[simp] theorem formalPoint_formalParameter {k : ℕ} (P : filtration hW k) :
    formalPoint hW (formalParameter hW P) = P := by
  change ((formalParameterEquiv hW) ((formalParameterEquiv hW).symm _) : W.Point) = P
  simp

@[simp] theorem formalParameter_add {k : ℕ} (P Q : filtration hW k) :
    formalParameter hW (P + Q) = formalParameter hW P + formalParameter hW Q := by
  simp [formalParameter]

/-- Integral parameter `-x/y`, with value zero at infinity. -/
noncomputable def parameter {k : ℕ} (P : filtration hW k) : v.adicCompletionIntegers K :=
  formalParameter hW P ()

@[simp] theorem parameter_zero {k : ℕ} : parameter hW (0 : filtration hW k) = 0 := by
  simp [parameter, formalParameter]

theorem parameter_mem {k : ℕ} (P : filtration hW k) :
    parameter hW P ∈ maximalIdeal (v.adicCompletionIntegers K) ^ (k + 1) := by
  apply (mem_pow_iff_formalPoint_mem_filtration (hW := hW) (formalParameter hW P) k).mpr
  simpa using P.2

/-- The error in parameter additivity has twice the input depth. -/
theorem parameter_add_error {k : ℕ} (P Q : filtration hW k) :
    parameter hW (P + Q) - (parameter hW P + parameter hW Q) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (2 * (k + 1)) := by
  change ((formalParameter hW (P + Q)) () : v.adicCompletionIntegers K) - _ ∈ _
  rw [formalParameter_add, W₀.add_apply_coe_eq_addEval]
  exact W₀.addEval_sub_add_mem (Nat.succ_ne_zero k) (parameter_mem hW P) (parameter_mem hW Q)

/-- The chosen formal parameter is literally `-x/y` in the completion. -/
theorem parameter_eq_neg_x_div_y {k : ℕ} (P : filtration hW k)
    {x y : v.adicCompletion K} {h : W.Nonsingular x y}
    (hP : (P : W.Point) = .some x y h) :
    (parameter hW P : v.adicCompletion K) = -x / y := by
  have hp := formalPoint_formalParameter hW P
  rw [hP] at hp
  have ht : parameter hW P ≠ 0 := by
    intro hz
    rw [formalPoint_of_param_eq_zero hW hz] at hp
    cases hp
  rw [formalPoint_of_param_ne_zero hW ht] at hp
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hp
  obtain ⟨hx, hy⟩ := hp
  rw [← hx, ← hy]
  have hw : ((W₀.wEval (formalParameter hW P ()) : v.adicCompletionIntegers K) :
      v.adicCompletion K) ≠ 0 := by
    exact_mod_cast (W₀.wEval_ne_zero (formalParameter hW P ()).2 ht)
  dsimp [parameter]
  field_simp [hw]

variable (hmax : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {(2 : v.adicCompletionIntegers K)})

include hmax

/-- Divisibility of the actual parameter by the chosen power of two. -/
theorem parameter_two_pow_dvd {k : ℕ} (P : filtration hW k) :
    (2 : v.adicCompletionIntegers K) ^ (k+1) ∣ parameter hW P := by
  have ht := parameter_mem hW P
  rwa [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ht

/-- `z(P)/2^(k+1)` as an integral element of the completion. -/
noncomputable def scaledParameter {k : ℕ} (P : filtration hW k) : v.adicCompletionIntegers K :=
  Classical.choose (parameter_two_pow_dvd hW hmax P)

theorem parameter_eq_two_pow_mul {k : ℕ} (P : filtration hW k) :
    parameter hW P = 2^(k+1) * scaledParameter hW hmax P :=
  Classical.choose_spec (parameter_two_pow_dvd hW hmax P)

/-- The scaled parameter is well defined modulo four at every depth at least two. -/
theorem scaledParameter_add_error {k : ℕ} (hk : 1 ≤ k) (P Q : filtration hW k) :
    (4 : v.adicCompletionIntegers K) ∣
      scaledParameter hW hmax (P+Q) - (scaledParameter hW hmax P + scaledParameter hW hmax Q) := by
  have he := parameter_add_error hW P Q
  have he' : parameter hW (P+Q) - (parameter hW P + parameter hW Q) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ ((k+1)+2) :=
    (Ideal.pow_le_pow_right (by omega : (k+1)+2 ≤ 2*(k+1))) he
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at he'
  obtain ⟨w, hw⟩ := he'
  refine ⟨w, ?_⟩
  letI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  apply mul_left_cancel₀ (pow_ne_zero (k+1) (by norm_num : (2 : v.adicCompletionIntegers K) ≠ 0))
  rw [show (2 : v.adicCompletionIntegers K)^((k+1)+2) = 2^(k+1)*4 by rw [pow_add]; norm_num] at hw
  rw [parameter_eq_two_pow_mul hW hmax, parameter_eq_two_pow_mul hW hmax,
    parameter_eq_two_pow_mul hW hmax] at hw
  linear_combination hw

/-- The dyadic character is constructed from the actual formal parameter. -/
noncomputable def parameterCharacter {k : ℕ} (hk : 1 ≤ k)
    (res : v.adicCompletionIntegers K →+* ZMod 4) : filtration hW k →+ ZMod 4 :=
  AddMonoidHom.mk' (fun P => res (scaledParameter hW hmax P)) (fun P Q => by
    obtain ⟨w, hw⟩ := scaledParameter_add_error hW hmax hk P Q
    have hh := congrArg res hw
    simp only [map_sub, map_add, map_mul, map_ofNat] at hh
    rw [show (4 : ZMod 4) = 0 by decide, zero_mul] at hh
    exact sub_eq_zero.mp hh)

/-- A coordinate-level formula for the character constructed above. -/
theorem scaledParameter_coe_eq {k : ℕ} (P : filtration hW k) :
    (scaledParameter hW hmax P : v.adicCompletion K) =
      (parameter hW P : v.adicCompletion K) / 2^(k+1) := by
  letI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have h : (parameter hW P : v.adicCompletion K) =
      (2 : v.adicCompletion K)^(k+1) * (scaledParameter hW hmax P : v.adicCompletion K) := by
    have hc (t : v.adicCompletionIntegers K) :
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) t = (t : v.adicCompletion K) := rfl
    have h0 := congrArg (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
      (parameter_eq_two_pow_mul hW hmax P)
    rw [map_mul, map_pow, map_ofNat] at h0
    simpa only [hc] using h0
  rw [h]
  field_simp

/-- The mod-four character has the paper's scaled `-x/y` coordinate formula. -/
theorem scaledParameter_eq_neg_x_div_y {k : ℕ} (P : filtration hW k)
    {x y : v.adicCompletion K} {h : W.Nonsingular x y}
    (hP : (P : W.Point) = .some x y h) :
    (scaledParameter hW hmax P : v.adicCompletion K) = (-x/y)/2^(k+1) := by
  rw [scaledParameter_coe_eq, parameter_eq_neg_x_div_y hW P hP]

end FormalParameter
end FourCorner.CommonSource.Dyadic
