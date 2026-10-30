import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single

set_option autoImplicit false

universe u v

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv Divisor Divisor.degree Divisor.degree_single Divisor.IsPrincipal Divisor.mem_principal HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.deg_eq_one_of_isAlgClosed exists_canonicalDivisor_genus_riemannRoch RROpens.exists_effective_sub_add_smul_single_mem_principal"
namespace FFRepGlue
p2m_open "AlgebraicCurve"

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_list_sum_single_eq (hdeg : ∀ v : Place K F, v.deg = 1) :
    ∀ E : Divisor K F, 0 ≤ E →
      ∃ l : List (Place K F), (l.map fun v => Finsupp.single v (1 : ℤ)).sum = E ∧ (l.length : ℤ) = Divisor.degree E := by
  classical
  intro E
  induction E using Finsupp.induction with
  | zero => intro _; exact ⟨[], by simp, by simp⟩
  | single_add v n E hv hn ih =>
      intro hE
      have hEv : ∀ w, 0 ≤ (Finsupp.single v n + E) w := fun w => hE w
      have hn0 : 0 ≤ n := by
        have := hEv v
        rw [Finsupp.add_apply, Finsupp.single_eq_same] at this
        have hEv0 : E v = 0 := by simpa [Finsupp.mem_support_iff] using hv
        omega
      have hE' : 0 ≤ E := by
        intro w
        rcases eq_or_ne w v with rfl | hw
        · have hEv0 : E w = 0 := by simpa [Finsupp.mem_support_iff] using hv
          simp [hEv0]
        · have := hEv w
          have hs : (Finsupp.single v n) w = 0 := Finsupp.single_eq_of_ne hw
          rw [Finsupp.add_apply, hs, zero_add] at this
          simpa using this
      obtain ⟨l, hl, hlen⟩ := ih hE'
      refine ⟨List.replicate n.toNat v ++ l, ?_, ?_⟩
      · rw [List.map_append, List.sum_append, hl, List.map_replicate, List.sum_replicate, ← Finsupp.smul_single_one v n]
        congr 1
        rw [← natCast_zsmul, Int.toNat_of_nonneg hn0]
      · rw [List.length_append, List.length_replicate, Nat.cast_add, hlen, map_add, Divisor.degree_single, hdeg, Nat.cast_one,
          mul_one, Int.toNat_of_nonneg hn0]

end AlgebraicCurve.FFRepGlue

open AlgebraicCurve.FFRepGlue in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (v₀ : Place K F) (D : Divisor K F) (hD : Divisor.degree D = 0) :
    ∃ l : List (Place K F),
      Divisor.IsPrincipal
        (D - ((l.map fun v => Finsupp.single v (1 : ℤ)).sum - (l.length : ℤ) • Finsupp.single v₀ 1)) := by
  classical
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨Kc, g, hRR⟩ := AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch K F

  obtain ⟨E, hE0, hE⟩ :=
    AlgebraicCurve.RROpens.exists_effective_sub_add_smul_single_mem_principal g Kc hRR v₀ (hdeg1 v₀) D hD
  obtain ⟨f, hf, hfE⟩ := (Divisor.mem_principal.mp hE)
  obtain ⟨Pf, hPf, hPfdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf

  obtain ⟨l, hl, hlen⟩ := exists_list_sum_single_eq hdeg1 E (fun v => hE0 v)
  have hEeq : E = (D + (g : ℤ) • Finsupp.single v₀ 1) + Pf := by
    ext v
    have := hfE v
    rw [Finsupp.sub_apply] at this
    rw [Finsupp.add_apply, hPf v]
    linarith
  have hlen' : (l.length : ℤ) = g := by
    rw [hlen, hEeq, map_add, map_add, hD, hPfdeg, map_zsmul, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one,
      smul_eq_mul, mul_one, zero_add, add_zero]
  refine ⟨l, f⁻¹, inv_ne_zero hf, fun v => ?_⟩
  rw [hl, hlen', Place.ord_inv, ← hfE v]
  simp only [Finsupp.sub_apply, Finsupp.add_apply]
  ring
