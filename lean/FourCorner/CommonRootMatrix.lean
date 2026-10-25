import FourCorner.CommonRootSupport
import FourCorner.CommonRootDyadic
import FourCorner.CommonRootRamified
import FourCorner.CommonRootMatrixLegendre
import FourCorner.CommonRootMatrixDyadic
import FourCorner.CommonRootMatrixDiscriminant

namespace FourCorner.CommonRootSource

/-- The ramified source equations force the row conditions for the actual
selected prime mask, including every complementary class. -/
theorem matrix_kernel_of_mask_squareclass {t : ℚ} (S : CommonRootSource ℚ t)
    {r : ℕ} (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hpodd : ∀ i, p i ≠ 2)
    (e : Fin r → ZMod 2) {qD qE : ℚ} (hqD : qD ≠ 0) (hqE : qE ≠ 0)
    (hd : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2)
    (he : S.ell = (2 * commonRootMaskProduct p e : ℕ) * qE ^ 2) :
    (primeLegendreMatrix p hp).mulVec e = 0 := by
  apply primeLegendreMatrix_mulVec_eq_zero_of_local p hp hinj e
  intro i
  let : Fact (p i).Prime := ⟨hp i⟩
  have hpi : p i ∣ ∏ j, p j := Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  have hdP : (t : ℚ_[p i]) ^ 2 - 1 = ((∏ j, p j : ℕ) : ℚ_[p i]) * (qD : ℚ_[p i]) ^ 2 := by
    exact_mod_cast hd
  obtain ⟨hodd, hpos⟩ := (S.toPadic (p i)).discriminant_valuation_odd_pos_of_squarefree
    (commonRootPrimeProduct_squarefree p hp hinj) hpi hqD hdP
  obtain ⟨h2, hlocal⟩ := (S.toPadic (p i)).ramified_square_classes (hpodd i) hpos hodd
  have hqEP : (qE : ℚ_[p i]) ≠ 0 := by exact_mod_cast hqE
  have hqDP : (qD : ℚ_[p i]) ≠ 0 := by exact_mod_cast hqD
  have hmP : (commonRootMaskProduct p e : ℚ_[p i]) ≠ 0 := by
    exact_mod_cast commonRootMaskProduct_ne_zero p hp e
  have heP : (S.toPadic (p i)).ell =
      2 * (commonRootMaskProduct p e : ℚ_[p i]) * (qE : ℚ_[p i]) ^ 2 := by
    change (S.ell : ℚ_[p i]) = _
    exact_mod_cast he
  have hdP' : (t : ℚ_[p i]) ^ 2 - 1 =
      (commonRootMaskProduct p e : ℚ_[p i]) *
      (commonRootMaskProduct p (commonRootMaskComplement e) : ℚ_[p i]) *
      (qD : ℚ_[p i]) ^ 2 := by
    rw [hdP, ← commonRootMaskProduct_complement_mul p e, Nat.cast_mul]
  have hs := commonRoot_remove_square_factors hqEP hqDP hmP (by norm_num : (2 : ℚ_[p i]) ≠ 0)
    heP hdP' hlocal
  rcases hs with hs | hs
  · have hs' : IsSquare ((2 * commonRootMaskProduct p e : ℕ) : ℚ_[p i]) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs
    obtain ⟨hunit, hchar⟩ := squarefree_padic_twice_square_unit_character (hpodd i)
      (commonRootMaskProduct_squarefree p hp hinj e) h2 hs'
    have hei : e i = 0 := by
      have hn := (commonRootMaskProduct_prime_dvd_iff p hp hinj e i).not.mp hunit
      rcases commonRoot_zmod_two_cases (e i) with h | h
      · exact h
      · exact (hn h).elim
    exact Or.inl ⟨hei, hchar⟩
  · have hs' : IsSquare ((2 * commonRootMaskProduct p (commonRootMaskComplement e) : ℕ) : ℚ_[p i]) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs
    obtain ⟨hunit, hchar⟩ := squarefree_padic_twice_square_unit_character (hpodd i)
      (commonRootMaskProduct_squarefree p hp hinj (commonRootMaskComplement e)) h2 hs'
    have hei : e i = 1 := by
      have hn := (commonRootMaskProduct_complement_prime_dvd_iff p hp hinj e i).not.mp hunit
      rcases commonRoot_zmod_two_cases (e i) with h | h
      · exact (hn h).elim
      · exact h
    exact Or.inr ⟨hei, hchar⟩

/-- Proposition common-matrix: every actual rational source has one global
binary prime allocation, with dyadic exponent one, in the residue-matrix
kernel. All support, dyadic, and ramified restrictions are derived here. -/
theorem residue_matrix_squareclass {t : ℚ} (S : CommonRootSource ℚ t)
    (ht : 1 < t) {r : ℕ} (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta : (∏ i, p i) % 8 = 1) {qD : ℚ}
    (hd : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2) :
    ∃ (e : Fin r → ZMod 2) (q : ℚ), 0 < q ∧
      S.ell = (2 * commonRootMaskProduct p e : ℕ) * q ^ 2 ∧
      (primeLegendreMatrix p hp).mulVec e = 0 := by
  have hqD : qD ≠ 0 := by
    intro hz
    rw [hz] at hd
    norm_num at hd
    nlinarith
  have hpodd : ∀ i, p i ≠ 2 := by
    intro i hi
    have hh := hpmod i
    simp [hi] at hh
  obtain ⟨n, hn, hns, hsupport, q, hq, he⟩ := S.positive_squareclass_support ht
  have hmaskSupport : ∀ l : ℕ, l.Prime → l ∣ n → l = 2 ∨ ∃ i, l = p i := by
    intro l hl hln
    rcases hsupport l hl hln with heq | hodd
    · exact Or.inl heq
    · right
      let : Fact l.Prime := ⟨hl⟩
      have hdiv : l ∣ ∏ i, p i := prime_dvd_nat_of_odd_rat_square_factor hqD hd hodd.2
      obtain ⟨i, _, hi⟩ := (hl.prime.dvd_finsetProd_iff p).mp hdiv
      exact ⟨i, (((hp i).dvd_iff_eq hl.ne_one).mp hi).symm⟩
  have htwo : 2 ∣ n := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hds : IsSquare ((t : ℚ_[2]) ^ 2 - 1) := by
      simpa using padic_two_isSquare_rat_of_nat_squareclass (t ^ 2 - 1) qD (∏ i, p i) hd hDelta
    obtain ⟨hv, _, hodd⟩ := (S.toPadic 2).dyadic_square_d_valuation hds
    have hellodd : Odd (padicValRat 2 S.ell) := by
      rw [← hv] at hodd
      simpa only [toPadic_ell, Padic.valuation_ratCast] using hodd
    exact prime_dvd_nat_of_odd_rat_square_factor (ne_of_gt hq) he hellodd
  obtain ⟨e, heq⟩ := commonRootMaskProduct_exists_of_squarefree p hp hinj hpodd hns htwo hmaskSupport
  have hell : S.ell = (2 * commonRootMaskProduct p e : ℕ) * q ^ 2 := by rwa [heq] at he
  exact ⟨e, q, hq, hell, S.matrix_kernel_of_mask_squareclass p hp hinj hpodd e hqD
    (ne_of_gt hq) hd hell⟩

/-- The binary-exponent form of the exact global squareclass assertion. -/
theorem residue_matrix_squareclass_exponents {t : ℚ} (S : CommonRootSource ℚ t)
    (ht : 1 < t) {r : ℕ} (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta : (∏ i, p i) % 8 = 1) {qD : ℚ}
    (hd : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2) :
    ∃ (e : Fin r → ZMod 2) (q : ℚ), 0 < q ∧
      S.ell = (2 * (∏ i, p i ^ (e i).val) : ℕ) * q ^ 2 ∧
      (primeLegendreMatrix p hp).mulVec e = 0 := by
  simpa only [commonRootMaskProduct_eq_prod_pow] using
    S.residue_matrix_squareclass ht p hp hinj hpmod hDelta hd

/-- The actual rank condition leaves precisely the two global rational
squareclasses [2] and [2 Delta], with a positive rational square witness. -/
theorem residue_matrix_two_classes {t : ℚ} (S : CommonRootSource ℚ t)
    (ht : 1 < t) {r : ℕ} (hr : 0 < r) (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta : (∏ i, p i) % 8 = 1) {qD : ℚ}
    (hd : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2)
    (hrank : (primeLegendreMatrix p hp).rank = r - 1) :
    ∃ q : ℚ, 0 < q ∧
      (S.ell = 2 * q ^ 2 ∨ S.ell = (2 * (∏ i, p i) : ℕ) * q ^ 2) := by
  obtain ⟨e, q, hq, hell, hker⟩ := S.residue_matrix_squareclass ht p hp hinj hpmod hDelta hd
  have heq := (matrix_kernel_eq_zero_or_one hr (primeLegendreMatrix p hp)
    (rowZeroMatrix_row_sum (primeLegendreEntries p hp)) hrank e).mp hker
  refine ⟨q, hq, ?_⟩
  rcases heq with heq | heq
  · left
    simpa [heq, commonRootMaskProduct] using hell
  · right
    simpa [heq, commonRootMaskProduct] using hell

/-- Full Proposition common-matrix in the paper's nontrivial-product form. -/
theorem residue_matrix_proposition {t : ℚ} (S : CommonRootSource ℚ t)
    (ht : 1 < t) {r : ℕ} (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta_gt : 1 < ∏ i, p i) (hDelta : (∏ i, p i) % 8 = 1) {qD : ℚ}
    (hd : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2) :
    (∃ (e : Fin r → ZMod 2) (q : ℚ), 0 < q ∧
      S.ell = (2 * (∏ i, p i ^ (e i).val) : ℕ) * q ^ 2 ∧
      (primeLegendreMatrix p hp).mulVec e = 0) ∧
    ((primeLegendreMatrix p hp).rank = r - 1 →
      ∃ q : ℚ, 0 < q ∧
        (S.ell = 2 * q ^ 2 ∨ S.ell = (2 * (∏ i, p i) : ℕ) * q ^ 2)) := by
  refine ⟨S.residue_matrix_squareclass_exponents ht p hp hinj hpmod hDelta hd, ?_⟩
  intro hrank
  have hr : 0 < r := by
    by_contra hh
    have hz : r = 0 := by omega
    subst r
    simp at hDelta_gt
  exact S.residue_matrix_two_classes ht hr p hp hinj hpmod hDelta hd hrank

end FourCorner.CommonRootSource

#print axioms FourCorner.CommonRootSource.matrix_kernel_of_mask_squareclass

#print axioms FourCorner.CommonRootSource.residue_matrix_squareclass
#print axioms FourCorner.CommonRootSource.residue_matrix_squareclass_exponents
#print axioms FourCorner.CommonRootSource.residue_matrix_two_classes

#print axioms FourCorner.CommonRootSource.residue_matrix_proposition
