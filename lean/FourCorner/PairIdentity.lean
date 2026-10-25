import FourCorner.GaussianCorners

set_option autoImplicit false

namespace FourCorner

/-- The algebra behind the six pair identities, for arbitrary integral
Gaussian roots and natural multipliers. -/
theorem gaussian_pair_identity (m n : ℕ) (q r : GaussianInt) :
    ((m : ℤ) * Zsqrtd.norm q + (n : ℤ) * Zsqrtd.norm r) ^ 2 -
      4 * ((m : ℤ) * n) * (q * star r).re ^ 2 =
    Zsqrtd.norm ((m : GaussianInt) * q ^ 2 - (n : GaussianInt) * r ^ 2) := by
  simp [Zsqrtd.norm, pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

namespace IntegralModel

/-- The squared distance between two corners of the unit square, with the
Boolean coordinates interpreted as the integers zero and one. -/
def cornerDistanceSquared (c c' : Bool × Bool) : ℤ :=
  ((if c.1 then 1 else 0) - (if c'.1 then 1 else 0)) ^ 2 +
    ((if c.2 then 1 else 0) - (if c'.2 then 1 else 0)) ^ 2

theorem cornerDistanceSquared_one_or_two {c c' : Bool × Bool} (hne : c ≠ c') :
    cornerDistanceSquared c c' = 1 ∨ cornerDistanceSquared c c' = 2 := by
  rcases c with ⟨e, h⟩
  rcases c' with ⟨e', h'⟩
  cases e <;> cases h <;> cases e' <;> cases h' <;>
    first | exact (hne rfl).elim | norm_num [cornerDistanceSquared]

/-- The signed displacements retain the exact separation between the
original labelled corners. -/
theorem corner_separation_sq (M : IntegralModel) (c c' : Bool × Bool) :
    (M.cornerX c.1 - M.cornerX c'.1) ^ 2 +
      (M.cornerY c.2 - M.cornerY c'.2) ^ 2 =
    cornerDistanceSquared c c' * M.L ^ 2 := by
  rcases c with ⟨e, h⟩
  rcases c' with ⟨e', h'⟩
  cases e <;> cases h <;> cases e' <;> cases h' <;>
    simp [cornerX, cornerY, cornerDistanceSquared] <;> ring

/-- Manuscript lemma `profile-pair-identity`: the integer identity for any
two original labelled corners and any Gaussian roots satisfying the signed
displacement and radius equations. -/
theorem corner_pair_identity (M : IntegralModel) (c c' : Bool × Bool)
    (q r : GaussianInt)
    (hq : (⟨M.cornerX c.1, M.cornerY c.2⟩ : GaussianInt) =
      (M.cornerClass c : GaussianInt) * q ^ 2)
    (hr : (⟨M.cornerX c'.1, M.cornerY c'.2⟩ : GaussianInt) =
      (M.cornerClass c' : GaussianInt) * r ^ 2)
    (hqn : M.cornerRadius c = (M.cornerClass c : ℤ) * Zsqrtd.norm q)
    (hrn : M.cornerRadius c' = (M.cornerClass c' : ℤ) * Zsqrtd.norm r) :
    (M.cornerRadius c + M.cornerRadius c') ^ 2 -
      4 * ((M.cornerClass c : ℤ) * M.cornerClass c') * (q * star r).re ^ 2 =
    cornerDistanceSquared c c' * M.L ^ 2 := by
  rw [hqn, hrn, gaussian_pair_identity, ← hq, ← hr]
  calc
    _ = (M.cornerX c.1 - M.cornerX c'.1) ^ 2 +
        (M.cornerY c.2 - M.cornerY c'.2) ^ 2 := by
      simp [Zsqrtd.norm, pow_two]
      ring
    _ = _ := M.corner_separation_sq c c'

/-- Dividing the integer pair identity by the common side squared yields
the rational norm equation in the manuscript. -/
theorem corner_pair_identity_normalized (M : IntegralModel) (c c' : Bool × Bool)
    (q r : GaussianInt)
    (hq : (⟨M.cornerX c.1, M.cornerY c.2⟩ : GaussianInt) =
      (M.cornerClass c : GaussianInt) * q ^ 2)
    (hr : (⟨M.cornerX c'.1, M.cornerY c'.2⟩ : GaussianInt) =
      (M.cornerClass c' : GaussianInt) * r ^ 2)
    (hqn : M.cornerRadius c = (M.cornerClass c : ℤ) * Zsqrtd.norm q)
    (hrn : M.cornerRadius c' = (M.cornerClass c' : ℤ) * Zsqrtd.norm r) :
    ((M.cornerRadius c : ℚ) / M.L + (M.cornerRadius c' : ℚ) / M.L) ^ 2 -
      ((M.cornerClass c : ℚ) * M.cornerClass c') *
        (2 * ((q * star r).re : ℚ) / M.L) ^ 2 =
    (cornerDistanceSquared c c' : ℚ) := by
  have hL : (M.L : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt M.L_pos)
  have hid : ((M.cornerRadius c : ℚ) + M.cornerRadius c') ^ 2 -
      4 * ((M.cornerClass c : ℚ) * M.cornerClass c') *
        ((q * star r).re : ℚ) ^ 2 =
      (cornerDistanceSquared c c' : ℚ) * (M.L : ℚ) ^ 2 := by
    exact_mod_cast M.corner_pair_identity c c' q r hq hr hqn hrn
  field_simp
  nlinarith [hid]

/-- A single family of the four canonical Gaussian roots satisfies all six
integer and rational pair identities. All roots are extracted from the
actual primitive integral model. -/
theorem six_pair_identities (M : IntegralModel) (hX : Odd M.X) :
    ∃ w : Bool × Bool → GaussianInt,
      (∀ c, w c ≠ 0 ∧
        (⟨M.cornerX c.1, M.cornerY c.2⟩ : GaussianInt) =
          (M.cornerClass c : GaussianInt) * w c ^ 2 ∧
        M.cornerRadius c = (M.cornerClass c : ℤ) * Zsqrtd.norm (w c) ∧
        0 < Zsqrtd.norm (w c)) ∧
      ∀ c c', c ≠ c' →
        (cornerDistanceSquared c c' = 1 ∨ cornerDistanceSquared c c' = 2) ∧
        (M.cornerRadius c + M.cornerRadius c') ^ 2 -
            4 * ((M.cornerClass c : ℤ) * M.cornerClass c') *
              (w c * star (w c')).re ^ 2 =
          cornerDistanceSquared c c' * M.L ^ 2 ∧
        ((M.cornerRadius c : ℚ) / M.L + (M.cornerRadius c' : ℚ) / M.L) ^ 2 -
            ((M.cornerClass c : ℚ) * M.cornerClass c') *
              (2 * ((w c * star (w c')).re : ℚ) / M.L) ^ 2 =
          (cornerDistanceSquared c c' : ℚ) := by
  have hL : Even M.L := even_iff_two_dvd.mpr
    (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  choose w hw hroot hnorm hpos using M.corner_gaussian_root hX hL
  refine ⟨w, fun c => ⟨hw c, hroot c, hnorm c, hpos c⟩, ?_⟩
  intro c c' hne
  exact ⟨cornerDistanceSquared_one_or_two hne,
    M.corner_pair_identity c c' (w c) (w c') (hroot c) (hroot c') (hnorm c) (hnorm c'),
    M.corner_pair_identity_normalized c c' (w c) (w c')
      (hroot c) (hroot c') (hnorm c) (hnorm c')⟩

end IntegralModel
end FourCorner

#print axioms FourCorner.gaussian_pair_identity
#print axioms FourCorner.IntegralModel.cornerDistanceSquared_one_or_two
#print axioms FourCorner.IntegralModel.corner_separation_sq
#print axioms FourCorner.IntegralModel.corner_pair_identity
#print axioms FourCorner.IntegralModel.corner_pair_identity_normalized
#print axioms FourCorner.IntegralModel.six_pair_identities
