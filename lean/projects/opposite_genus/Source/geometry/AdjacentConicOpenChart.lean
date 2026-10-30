import geometry.AdjacentConicChart

noncomputable section
namespace FourCorner.AdjacentConic.Chart

variable {K : Type*} [Field K] [CharZero K]

/-- Parameters at which the displayed affine chart is defined. -/
def Parameters (c : K) := {t : K // denominator c t ≠ 0}

/-- Literal affine conic points in the complement of the chart's basepoint. -/
def Points (c : K) :=
  {p : K × K // (c ^ 2 - 1) * p.1 ^ 2 + c ^ 2 * p.2 ^ 2 - c ^ 2 * (c ^ 2 - 1) = 0 ∧
    c - p.1 ≠ 0}

/-- The two explicit formulas and the slope inverse give a genuine bijection. -/
def openChartEquiv (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    Parameters c ≃ Points c where
  toFun t := ⟨(u c t.1, v c t.1), conic_identity c t.1 t.2,
    c_sub_u_ne_zero c t.1 hc hA t.2⟩
  invFun p := ⟨p.1.2 / (c - p.1.1),
    denominator_inverse_ne_zero c p.1.1 p.1.2 hc hA p.2.1 p.2.2⟩
  left_inv t := Subtype.ext (inverse c t.1 hc hA t.2)
  right_inv p := Subtype.ext (Prod.ext
    (u_inverse c p.1.1 p.1.2 hc hA p.2.1 p.2.2)
    (v_inverse c p.1.1 p.1.2 hc hA p.2.1 p.2.2))

@[simp] theorem openChartEquiv_apply (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0)
    (t : Parameters c) : (openChartEquiv c hc hA t).1 = (u c t.1, v c t.1) := rfl

@[simp] theorem openChartEquiv_symm_apply (c : K) (hc : c ≠ 0)
    (hA : c ^ 2 - 1 ≠ 0) (p : Points c) :
    ((openChartEquiv c hc hA).symm p).1 = p.1.2 / (c - p.1.1) := rfl

omit [CharZero K] in
/-- The excluded condition is exactly the single affine point `(c,0)`. -/
theorem chart_condition_iff_ne_basepoint (c U V : K) (hc : c ≠ 0)
    (hconic : (c ^ 2 - 1) * U ^ 2 + c ^ 2 * V ^ 2 - c ^ 2 * (c ^ 2 - 1) = 0) :
    c - U ≠ 0 ↔ (U, V) ≠ (c, 0) := by
  constructor
  · intro h heq
    have hu : U = c := congrArg Prod.fst heq
    exact h (by rw [hu, sub_self])
  · intro h hz
    have hu : U = c := (sub_eq_zero.mp hz).symm
    have hv : V = 0 := omitted_point c U V hc hconic hu
    exact h (Prod.ext hu hv)

#print axioms openChartEquiv
#print axioms chart_condition_iff_ne_basepoint

end FourCorner.AdjacentConic.Chart
