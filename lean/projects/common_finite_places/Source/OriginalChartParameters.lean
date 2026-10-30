import OriginalFiniteChart

noncomputable section
namespace FourCorner.OriginalChartParameters
open RadicalLinearization Genus17Geometry
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

/-- The original free coordinates determine ell in all five finite branch
charts inside the SAME literal function field. -/
theorem finite_parameters (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0) :
    RadicalLinearization.ell k t κ= -(algebraMap k E (t+1))+fiveRoot t κ 0^2 ∧
    RadicalLinearization.ell k t κ= algebraMap k E (t-1)+fiveRoot t κ 1^2 ∧
    RadicalLinearization.ell k t κ= algebraMap k E ((t-1)*(t+1))/
      (algebraMap k E (t-1)+fiveRoot t κ 2^2) ∧
    RadicalLinearization.ell k t κ= algebraMap k E ((t+1)*(t-1))/
      (fiveRoot t κ 3^2-algebraMap k E (t+1)) ∧
    RadicalLinearization.ell k t κ=algebraMap k E κ * fiveRoot t κ 4^2 := by
  have he := RadicalLinearization.ell_ne_zero k t κ
  have hs : algebraMap k E (t-1)≠0 := (map_ne_zero _).mpr (sub_ne_zero.mpr h1)
  have hT : algebraMap k E (t+1)≠0 := by
    apply (map_ne_zero _).mpr
    intro h
    apply hm
    linear_combination h
  have hk : algebraMap k E κ≠0 := (map_ne_zero _).mpr hκ
  have hP := OriginalFiniteChart.original_sq (t:=t) (κ:=κ) (0:Fin 4)
  have hC := OriginalFiniteChart.original_sq (t:=t) (κ:=κ) (1:Fin 4)
  have hM := OriginalFiniteChart.original_sq (t:=t) (κ:=κ) (2:Fin 4)
  have hB := OriginalFiniteChart.original_sq (t:=t) (κ:=κ) (3:Fin 4)
  change fiveRoot t κ 0^2=RadicalLinearization.ell k t κ+(algebraMap k E t+1) at hP
  change fiveRoot t κ 1^2=RadicalLinearization.ell k t κ-(algebraMap k E t-1) at hC
  change fiveRoot t κ 2^2=(algebraMap k E t-1)*((algebraMap k E t+1)-RadicalLinearization.ell k t κ)*(RadicalLinearization.ell k t κ)⁻¹ at hM
  change fiveRoot t κ 3^2=(algebraMap k E t+1)*(RadicalLinearization.ell k t κ+(algebraMap k E t-1))*(RadicalLinearization.ell k t κ)⁻¹ at hB
  have hMs : RadicalLinearization.ell k t κ*(algebraMap k E (t-1)+fiveRoot t κ 2^2)=algebraMap k E ((t-1)*(t+1)) := by
    rw [hM,map_mul,map_sub,map_one,map_add]
    simp only [map_one]
    field_simp [he] <;> ring
  have hBs : RadicalLinearization.ell k t κ*(fiveRoot t κ 3^2-algebraMap k E (t+1))=algebraMap k E ((t+1)*(t-1)) := by
    rw [hB,map_mul,map_sub,map_one,map_add]
    simp only [map_one]
    field_simp [he] <;> ring
  have hMd : algebraMap k E (t-1)+fiveRoot t κ 2^2≠0 := by
    intro h
    rw [h,mul_zero,map_mul] at hMs
    exact (mul_ne_zero hs hT) hMs.symm
  have hBd : fiveRoot t κ 3^2-algebraMap k E (t+1)≠0 := by
    intro h
    rw [h,mul_zero,map_mul] at hBs
    exact (mul_ne_zero hT hs) hBs.symm
  refine ⟨?_,?_,(eq_div_iff hMd).mpr hMs,(eq_div_iff hBd).mpr hBs,?_⟩
  · rw [hP,map_add,map_one]; ring
  · rw [hC,map_sub,map_one]; ring
  · have hz := roots_sq k t κ hκ 4
    change fiveRoot t κ 4^2=RadicalLinearization.ell k t κ*algebraMap k E κ⁻¹ at hz
    rw [map_inv₀] at hz
    rw [hz]
    field_simp [hk]
end FourCorner.OriginalChartParameters
#print axioms FourCorner.OriginalChartParameters.finite_parameters
