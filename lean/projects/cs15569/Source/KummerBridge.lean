import GroupInterface
import OrderedKummer

/-! The actual Kummer map of `y² = x(x-n)(x+n)`, in root order `(0,n,-n)`. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial WeierstrassCurve.Affine

namespace FourCorner.CommonSource
noncomputable section

def kummerRoots (n : ℚ) : Fin 3 → ℚ := ![0, n, -n]

theorem kummerRoots_injective {n : ℚ} (hn : n ≠ 0) :
    Function.Injective (kummerRoots n) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [kummerRoots] at h ⊢ <;>
    (exfalso; apply hn; linarith)

theorem congruent_f_factorization (n : ℚ) :
    (congruentCurve n).toAffine.f = ∏ i : Fin 3, (X - C (kummerRoots n i)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [kummerRoots, f, congruentCurve]
  ring

instance congruentCurve_charNeTwoNF (n : ℚ) : (congruentCurve n).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

/-- Chinese remainder evaluation preserves the three named root coordinates. -/
def kummerCRT (n : ℚ) (hn : n ≠ 0) :
    (congruentCurve n).toAffine.A ≃ₐ[ℚ] (Fin 3 → ℚ) :=
  OrderedSplit.orderedEval (kummerRoots n) (kummerRoots_injective hn)
    (congruent_f_factorization n)

@[simp] theorem kummerCRT_mk (n : ℚ) (hn : n ≠ 0) (q : ℚ[X]) (i : Fin 3) :
    kummerCRT n hn (AdjoinRoot.mk (congruentCurve n).toAffine.f q) i =
      q.eval (kummerRoots n i) :=
  OrderedSplit.orderedEval_mk _ _ _ _ _

/-- The descent homomorphism of the actual Mathlib group, transported by CRT. -/
def kummerDelta (n : ℚ) (hn : n ≠ 0) :
    Multiplicative (Point n) →* (Fin 3 → Units.modPow ℚ 2) := by
  letI := isElliptic hn
  exact OrderedSplit.orderedDelta (kummerRoots n) (kummerRoots_injective hn)
    (congruent_f_factorization n)

/-- No Kummer-kernel hypothesis is assumed: the vendor theorem supplies it. -/
theorem kummerDelta_ker (n : ℚ) (hn : n ≠ 0) :
    (kummerDelta n hn).ker =
      (nsmulAddMonoidHom (α := Point n) 2).range.toSubgroup := by
  letI := isElliptic hn
  exact OrderedSplit.orderedDelta_ker _ _ _

theorem kummerDelta_eq_one_iff_double (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    kummerDelta n hn (Multiplicative.ofAdd P) = 1 ↔
      ∃ Q : Point n, 2 • Q = P := by
  letI := isElliptic hn
  exact OrderedSplit.orderedDelta_eq_one_iff_double _ _ _ P

@[simp] theorem kummerDelta_O (n : ℚ) (hn : n ≠ 0) :
    kummerDelta n hn (Multiplicative.ofAdd (O n)) = 1 :=
  map_one _

/-- The ordinary signed row retains the order `(x,x-n,x+n)`. -/
theorem kummerDelta_finitePoint {n x y : ℚ} (hn : n ≠ 0)
    (hP : CongruentEquation n x y) (hx : x ≠ 0) (hxm : x - n ≠ 0)
    (hxp : x + n ≠ 0) :
    kummerDelta n hn (Multiplicative.ofAdd (finitePoint hn hP)) =
      ![OrderedSplit.scalarClass x hx, OrderedSplit.scalarClass (x-n) hxm,
        OrderedSplit.scalarClass (x+n) hxp] := by
  letI := isElliptic hn
  have hf : (congruentCurve n).toAffine.f.eval x ≠ 0 := by
    have he : (congruentCurve n).toAffine.f.eval x = x * (x-n) * (x+n) := by
      simp [congruentCurve, WeierstrassCurve.toAffine]
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero hx hxm) hxp
  ext i
  change OrderedSplit.orderedDelta (kummerRoots n) (kummerRoots_injective hn)
    (congruent_f_factorization n) _ i = _
  unfold finitePoint
  rw [OrderedSplit.orderedDelta_some_of_nonroot _ _ _ (nonsingular hn hP) hf]
  fin_cases i <;> simp [kummerRoots]

theorem kummerDelta_at_zero (n : ℚ) (hn : n ≠ 0)
    (hxy : (congruentCurve n).toAffine.Nonsingular 0 0) :
    kummerDelta n hn (Multiplicative.ofAdd (Point.some 0 0 hxy)) =
      ![OrderedSplit.scalarClass (-1 : ℚ) (by norm_num),
        OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn), OrderedSplit.scalarClass n hn] := by
  letI := isElliptic hn
  ext i
  change OrderedSplit.orderedDelta (kummerRoots n) (kummerRoots_injective hn) (congruent_f_factorization n)
    (Multiplicative.ofAdd (Point.some (kummerRoots n 0) 0 hxy)) i = _
  rw [OrderedSplit.orderedDelta_some_at_root _ _ _ 0 hxy i]
  fin_cases i
  · apply OrderedSplit.scalarClass_eq_of_mul_square (q := n)
    simp [OrderedSplit.torsionRow, kummerRoots]
    ring
  · apply OrderedSplit.scalarClass_eq_of_mul_square (q := 1)
    simp [OrderedSplit.torsionRow, kummerRoots]
  · apply OrderedSplit.scalarClass_eq_of_mul_square (q := 1)
    simp [OrderedSplit.torsionRow, kummerRoots]

theorem kummerDelta_at_plus (n : ℚ) (hn : n ≠ 0)
    (hxy : (congruentCurve n).toAffine.Nonsingular n 0) :
    kummerDelta n hn (Multiplicative.ofAdd (Point.some n 0 hxy)) =
      ![OrderedSplit.scalarClass n hn, OrderedSplit.scalarClass (2 : ℚ) (by norm_num),
        OrderedSplit.scalarClass (2*n) (mul_ne_zero (by norm_num) hn)] := by
  letI := isElliptic hn
  ext i
  change OrderedSplit.orderedDelta (kummerRoots n) (kummerRoots_injective hn) (congruent_f_factorization n)
    (Multiplicative.ofAdd (Point.some (kummerRoots n 1) 0 hxy)) i = _
  rw [OrderedSplit.orderedDelta_some_at_root _ _ _ 1 hxy i]
  fin_cases i
  · apply OrderedSplit.scalarClass_eq_of_mul_square (q := 1)
    simp [OrderedSplit.torsionRow, kummerRoots]
  · apply OrderedSplit.scalarClass_eq_of_mul_square (q := n)
    simp [OrderedSplit.torsionRow, kummerRoots]
    ring
  · apply OrderedSplit.scalarClass_eq_of_mul_square (q := 1)
    simp [OrderedSplit.torsionRow, kummerRoots]
    ring

theorem kummerDelta_at_minus (n : ℚ) (hn : n ≠ 0)
    (hxy : (congruentCurve n).toAffine.Nonsingular (-n) 0) :
    kummerDelta n hn (Multiplicative.ofAdd (Point.some (-n) 0 hxy)) =
      ![OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn),
        OrderedSplit.scalarClass (-2*n) (mul_ne_zero (by norm_num) hn),
        OrderedSplit.scalarClass (2 : ℚ) (by norm_num)] := by
  letI := isElliptic hn
  ext i
  change OrderedSplit.orderedDelta (kummerRoots n) (kummerRoots_injective hn) (congruent_f_factorization n)
    (Multiplicative.ofAdd (Point.some (kummerRoots n 2) 0 hxy)) i = _
  rw [OrderedSplit.orderedDelta_some_at_root _ _ _ 2 hxy i]
  fin_cases i
  · apply OrderedSplit.scalarClass_eq_of_mul_square (q := 1)
    simp [OrderedSplit.torsionRow, kummerRoots]
  · apply OrderedSplit.scalarClass_eq_of_mul_square (q := 1)
    simp [OrderedSplit.torsionRow, kummerRoots]
    ring

  · apply OrderedSplit.scalarClass_eq_of_mul_square (q := n)
    simp [OrderedSplit.torsionRow, kummerRoots]
    ring

theorem kummerDelta_T0 (n : ℚ) (hn : n ≠ 0) :
    kummerDelta n hn (Multiplicative.ofAdd (T0 n hn)) =
      ![OrderedSplit.scalarClass (-1 : ℚ) (by norm_num),
        OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn), OrderedSplit.scalarClass n hn] :=
  kummerDelta_at_zero n hn _

theorem kummerDelta_Tplus (n : ℚ) (hn : n ≠ 0) :
    kummerDelta n hn (Multiplicative.ofAdd (Tplus n hn)) =
      ![OrderedSplit.scalarClass n hn, OrderedSplit.scalarClass (2 : ℚ) (by norm_num),
        OrderedSplit.scalarClass (2*n) (mul_ne_zero (by norm_num) hn)] :=
  kummerDelta_at_plus n hn _

theorem kummerDelta_Tminus (n : ℚ) (hn : n ≠ 0) :
    kummerDelta n hn (Multiplicative.ofAdd (Tminus n hn)) =
      ![OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn),
        OrderedSplit.scalarClass (-2*n) (mul_ne_zero (by norm_num) hn),
        OrderedSplit.scalarClass (2 : ℚ) (by norm_num)] :=
  kummerDelta_at_minus n hn _

/-- The full three-coordinate image obeys the product-one relation. -/
theorem kummerDelta_product (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    ∏ i, kummerDelta n hn (Multiplicative.ofAdd P) i = 1 := by
  letI := isElliptic hn
  exact OrderedSplit.orderedDelta_product _ _ _ P

/-- Equality of the first two coordinates suffices because the third is determined. -/
theorem kummerDelta_eq_iff_first_two (n : ℚ) (hn : n ≠ 0) (P Q : Point n) :
    kummerDelta n hn (Multiplicative.ofAdd P) =
      kummerDelta n hn (Multiplicative.ofAdd Q) ↔
    kummerDelta n hn (Multiplicative.ofAdd P) 0 =
      kummerDelta n hn (Multiplicative.ofAdd Q) 0 ∧
    kummerDelta n hn (Multiplicative.ofAdd P) 1 =
      kummerDelta n hn (Multiplicative.ofAdd Q) 1 := by
  letI := isElliptic hn
  exact OrderedSplit.orderedDelta_eq_iff_first_two _ _ _ P Q

theorem kummerDelta_add (n : ℚ) (hn : n ≠ 0) (P Q : Point n) :
    kummerDelta n hn (Multiplicative.ofAdd (P + Q)) =
      kummerDelta n hn (Multiplicative.ofAdd P) *
        kummerDelta n hn (Multiplicative.ofAdd Q) :=
  map_mul _ _ _

/-- Equality of actual descent classes is exactly equality modulo doubling. -/
theorem kummerDelta_eq_iff_coset (n : ℚ) (hn : n ≠ 0) (P Q : Point n) :
    kummerDelta n hn (Multiplicative.ofAdd P) =
      kummerDelta n hn (Multiplicative.ofAdd Q) ↔
    ∃ R : Point n, P = Q + 2 • R := by
  have hd : kummerDelta n hn (Multiplicative.ofAdd (P-Q)) = 1 ↔
      kummerDelta n hn (Multiplicative.ofAdd P) =
        kummerDelta n hn (Multiplicative.ofAdd Q) := by
    change kummerDelta n hn (Multiplicative.ofAdd P / Multiplicative.ofAdd Q) = 1 ↔ _
    rw [_root_.map_div, div_eq_one]
  rw [← hd, kummerDelta_eq_one_iff_double]
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R, by rw [hR]; abel⟩
  · rintro ⟨R, rfl⟩
    exact ⟨R, by abel⟩

/-- Under the paper's splitting, the halving point can be chosen in `H`. -/
theorem kummerDelta_eq_iff_subgroup_coset {n : ℚ} (hn : n ≠ 0)
    {H : AddSubgroup (Point n)} (hsplit : SplitsOverTwoTorsion n H) (P Q : Point n) :
    kummerDelta n hn (Multiplicative.ofAdd P) =
      kummerDelta n hn (Multiplicative.ofAdd Q) ↔
    ∃ Z ∈ H, P = Q + 2 • Z := by
  rw [kummerDelta_eq_iff_coset]
  constructor
  · rintro ⟨R, hR⟩
    have hd : ∃ R : Point n, 2 • R = P-Q := ⟨R, by rw [hR]; abel⟩
    obtain ⟨Z, hZ, hdouble⟩ := exists_double_in_subgroup hsplit hd
    exact ⟨Z, hZ, by rw [hdouble]; abel⟩
  · rintro ⟨Z, _, hZ⟩
    exact ⟨Z, hZ⟩

/-- The fixed ordered source class is `(-n,-n,1)`. -/
def commonKummerClass (n : ℚ) (hn : n ≠ 0) : Fin 3 → Units.modPow ℚ 2 :=
  ![OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn),
    OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn), 1]

/-- The simultaneous source squares give the actual Kummer class of the sum. -/
theorem source_kummer_sum {n a b c ℓ u v : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hR : CongruentEquation n c ℓ)
    (ha : a ≠ 0) (hc : c ≠ 0) (ham : a-n ≠ 0) (hcm : c-n ≠ 0)
    (hap : a+n ≠ 0) (hcp : c+n ≠ 0)
    (hu : u ^ 2 = -(a*c)/n) (hv : v ^ 2 = -((a-n)*(c-n))/n) :
    kummerDelta n hn (Multiplicative.ofAdd (finitePoint hn hQ + finitePoint hn hR)) =
      commonKummerClass n hn := by
  have h0 : a*c = -n * u^2 := by
    have h := (eq_div_iff hn).mp hu
    nlinarith
  have h1 : (a-n)*(c-n) = -n * v^2 := by
    have h := (eq_div_iff hn).mp hv
    nlinarith
  have h2 := ordinateW_square hn ha hc ham hcm hQ hR hu hv
  rw [kummerDelta_add, kummerDelta_finitePoint hn hQ ha ham hap,
    kummerDelta_finitePoint hn hR hc hcm hcp]
  ext i
  fin_cases i
  · change OrderedSplit.scalarClass a ha * OrderedSplit.scalarClass c hc =
      OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn)
    rw [OrderedSplit.scalarClass_mul]
    exact OrderedSplit.scalarClass_eq_of_mul_square _ _ h0
  · change OrderedSplit.scalarClass (a-n) ham * OrderedSplit.scalarClass (c-n) hcm =
      OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn)
    rw [OrderedSplit.scalarClass_mul]
    exact OrderedSplit.scalarClass_eq_of_mul_square _ _ h1
  · change OrderedSplit.scalarClass (a+n) hap * OrderedSplit.scalarClass (c+n) hcp = 1
    rw [OrderedSplit.scalarClass_mul, OrderedSplit.scalarClass_eq_one_iff]
    exact ⟨ordinateW n b ℓ u v, by simpa only [pow_two] using h2.symm⟩

/-- The two source-square conditions are equivalent to the actual Kummer sum class. -/
theorem source_squares_iff_kummer_sum {n a b c ℓ : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hR : CongruentEquation n c ℓ)
    (ha : a ≠ 0) (hc : c ≠ 0) (ham : a-n ≠ 0) (hcm : c-n ≠ 0)
    (hap : a+n ≠ 0) (hcp : c+n ≠ 0) :
    (∃ u v : ℚ, u ^ 2 = -(a*c)/n ∧ v ^ 2 = -((a-n)*(c-n))/n) ↔
    kummerDelta n hn (Multiplicative.ofAdd (finitePoint hn hQ + finitePoint hn hR)) =
      commonKummerClass n hn := by
  constructor
  · rintro ⟨u, v, hu, hv⟩
    exact source_kummer_sum hn hQ hR ha hc ham hcm hap hcp hu hv
  · intro h
    rw [kummerDelta_add, kummerDelta_finitePoint hn hQ ha ham hap,
      kummerDelta_finitePoint hn hR hc hcm hcp] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change OrderedSplit.scalarClass a ha * OrderedSplit.scalarClass c hc =
      OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn) at h0
    change OrderedSplit.scalarClass (a-n) ham * OrderedSplit.scalarClass (c-n) hcm =
      OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn) at h1
    rw [OrderedSplit.scalarClass_mul, OrderedSplit.scalarClass_eq_iff_exists] at h0 h1
    obtain ⟨u, hu⟩ := h0
    obtain ⟨v, hv⟩ := h1
    refine ⟨u, v, (eq_div_iff hn).mpr ?_, (eq_div_iff hn).mpr ?_⟩ <;> nlinarith

/-- Two ordered sources have sums in the same actual doubling coset. -/
theorem common_class_coset (n : ℚ) (hn : n ≠ 0) (P Q : Point n)
    (hP : kummerDelta n hn (Multiplicative.ofAdd P) = commonKummerClass n hn)
    (hQ : kummerDelta n hn (Multiplicative.ofAdd Q) = commonKummerClass n hn) :
    ∃ R : Point n, P = Q + 2 • R :=
  (kummerDelta_eq_iff_coset n hn P Q).mp (hP.trans hQ.symm)

/-- The complete source-to-coset step for the `(-n,-n)` distinguished row. -/
theorem source_coset_of_torsion_sum_zero {n a b c ℓ u v : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hR : CongruentEquation n c ℓ)
    (ha : a ≠ 0) (hc : c ≠ 0) (ham : a-n ≠ 0) (hcm : c-n ≠ 0)
    (hap : a+n ≠ 0) (hcp : c+n ≠ 0)
    (hu : u ^ 2 = -(a*c)/n) (hv : v ^ 2 = -((a-n)*(c-n))/n)
    {H : AddSubgroup (Point n)} (hcompl : IsCompl H (twoTorsion n))
    (U V W τQ τR : Point n)
    (hU : finitePoint hn hQ = U + τQ) (hV : finitePoint hn hR = V + τR)
    (hτ : τQ + τR = 0)
    (hW0 : kummerDelta n hn (Multiplicative.ofAdd W) 0 =
      OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn))
    (hW1 : kummerDelta n hn (Multiplicative.ofAdd W) 1 =
      OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn)) :
    ∃ Z ∈ H, U + V = W + 2 • Z := by
  have hs := source_kummer_sum hn hQ hR ha hc ham hcm hap hcp hu hv
  have hδ : kummerDelta n hn
      (Multiplicative.ofAdd (finitePoint hn hQ + finitePoint hn hR)) =
        kummerDelta n hn (Multiplicative.ofAdd W) := by
    apply (kummerDelta_eq_iff_first_two n hn _ _).mpr
    constructor
    · rw [hs, hW0]; rfl
    · rw [hs, hW1]; rfl
  obtain ⟨Z, hZ, heq⟩ := (kummerDelta_eq_iff_subgroup_coset hn
    (splitsOverTwoTorsion_of_isCompl hcompl) _ _).mp hδ
  refine ⟨Z, hZ, ?_⟩
  rw [hU, hV] at heq
  calc
    U + V = (U + τQ) + (V + τR) := by rw [show (U + τQ) + (V + τR) = U+V+(τQ+τR) by abel, hτ, add_zero]
    _ = W + 2 • Z := heq

/-- The complete source-to-coset step for the `(n,1)` distinguished row.
The actual torsion row of `T0` converts it to `(-n,-n)`. -/
theorem source_coset_of_torsion_sum_T0 {n a b c ℓ u v : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hR : CongruentEquation n c ℓ)
    (ha : a ≠ 0) (hc : c ≠ 0) (ham : a-n ≠ 0) (hcm : c-n ≠ 0)
    (hap : a+n ≠ 0) (hcp : c+n ≠ 0)
    (hu : u ^ 2 = -(a*c)/n) (hv : v ^ 2 = -((a-n)*(c-n))/n)
    {H : AddSubgroup (Point n)} (hcompl : IsCompl H (twoTorsion n))
    (U V W τQ τR : Point n)
    (hU : finitePoint hn hQ = U + τQ) (hV : finitePoint hn hR = V + τR)
    (hτ : τQ + τR = T0 n hn)
    (hW0 : kummerDelta n hn (Multiplicative.ofAdd W) 0 =
      OrderedSplit.scalarClass n hn)
    (hW1 : kummerDelta n hn (Multiplicative.ofAdd W) 1 = 1) :
    ∃ Z ∈ H, U + V = W + 2 • Z := by
  have hs := source_kummer_sum hn hQ hR ha hc ham hcm hap hcp hu hv
  have hδ : kummerDelta n hn
      (Multiplicative.ofAdd (finitePoint hn hQ + finitePoint hn hR)) =
        kummerDelta n hn (Multiplicative.ofAdd (W + T0 n hn)) := by
    apply (kummerDelta_eq_iff_first_two n hn _ _).mpr
    constructor
    · rw [hs, kummerDelta_add, Pi.mul_apply, hW0, kummerDelta_T0]
      change OrderedSplit.scalarClass (-n) (neg_ne_zero.mpr hn) =
        OrderedSplit.scalarClass n hn * OrderedSplit.scalarClass (-1 : ℚ) (by norm_num)
      rw [OrderedSplit.scalarClass_mul]
      apply OrderedSplit.scalarClass_eq_of_mul_square (q := 1)
      ring
    · rw [hs, kummerDelta_add, Pi.mul_apply, hW1, kummerDelta_T0, one_mul]
      rfl
  obtain ⟨Z, hZ, heq⟩ := (kummerDelta_eq_iff_subgroup_coset hn
    (splitsOverTwoTorsion_of_isCompl hcompl) _ _).mp hδ
  refine ⟨Z, hZ, ?_⟩
  rw [hU, hV] at heq
  have hleft : (U+V) + T0 n hn = (W + 2 • Z) + T0 n hn := by
    calc
      (U+V) + T0 n hn = (U+τQ) + (V+τR) := by rw [← hτ]; abel
      _ = (W + T0 n hn) + 2 • Z := heq
      _ = (W + 2 • Z) + T0 n hn := by abel
  exact add_right_cancel hleft

#print axioms kummerCRT
#print axioms kummerDelta_ker
#print axioms kummerDelta_eq_one_iff_double
#print axioms kummerDelta_finitePoint
#print axioms kummerDelta_T0
#print axioms kummerDelta_Tplus
#print axioms kummerDelta_Tminus
#print axioms kummerDelta_product
#print axioms kummerDelta_eq_iff_first_two
#print axioms kummerDelta_eq_iff_coset
#print axioms kummerDelta_eq_iff_subgroup_coset
#print axioms source_kummer_sum
#print axioms source_squares_iff_kummer_sum
#print axioms common_class_coset
#print axioms source_coset_of_torsion_sum_zero
#print axioms source_coset_of_torsion_sum_T0

end
end FourCorner.CommonSource
