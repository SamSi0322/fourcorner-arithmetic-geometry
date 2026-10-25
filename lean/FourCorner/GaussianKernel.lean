import FourCorner.GaussianCorners

namespace FourCorner.IntegralModel

/-- Product of the four canonical squarefree corner contents. -/
noncomputable def cornerKernel (M : IntegralModel) : ℕ :=
  M.cornerClass (false, false) * M.cornerClass (true, false) *
    M.cornerClass (false, true) * M.cornerClass (true, true)

theorem cornerKernel_pos (M : IntegralModel) : 0 < M.cornerKernel := by
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (M.cornerClass_pos _) (M.cornerClass_pos _))
    (M.cornerClass_pos _)) (M.cornerClass_pos _)

theorem cornerKernel_odd (M : IntegralModel) (hX : Odd M.X) : Odd M.cornerKernel := by
  have hL : Even M.L := even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  exact (((M.cornerClass_odd hX hL _).mul (M.cornerClass_odd hX hL _)).mul
    (M.cornerClass_odd hX hL _)).mul (M.cornerClass_odd hX hL _)

theorem cornerKernel_coprime_side (M : IntegralModel) :
    M.cornerKernel.Coprime M.L.natAbs := by
  exact ((M.cornerClass_coprime_side _).mul_left (M.cornerClass_coprime_side _)).mul_left
    (M.cornerClass_coprime_side _) |>.mul_left (M.cornerClass_coprime_side _)

theorem cornerKernel_squarefree (M : IntegralModel) : Squarefree M.cornerKernel := by
  have h01 : (M.cornerClass (false, false)).Coprime (M.cornerClass (true, false)) :=
    M.cornerClass_pairwise_coprime (by decide)
  have h02 : (M.cornerClass (false, false)).Coprime (M.cornerClass (false, true)) :=
    M.cornerClass_pairwise_coprime (by decide)
  have h03 : (M.cornerClass (false, false)).Coprime (M.cornerClass (true, true)) :=
    M.cornerClass_pairwise_coprime (by decide)
  have h12 : (M.cornerClass (true, false)).Coprime (M.cornerClass (false, true)) :=
    M.cornerClass_pairwise_coprime (by decide)
  have h13 : (M.cornerClass (true, false)).Coprime (M.cornerClass (true, true)) :=
    M.cornerClass_pairwise_coprime (by decide)
  have h23 : (M.cornerClass (false, true)).Coprime (M.cornerClass (true, true)) :=
    M.cornerClass_pairwise_coprime (by decide)
  exact (Nat.squarefree_mul ((h03.mul_left h13).mul_left h23)).mpr
    ⟨(Nat.squarefree_mul (h02.mul_left h12)).mpr
      ⟨(Nat.squarefree_mul h01).mpr ⟨M.cornerClass_squarefree _, M.cornerClass_squarefree _⟩,
        M.cornerClass_squarefree _⟩, M.cornerClass_squarefree _⟩

theorem cornerKernel_prime_support (M : IntegralModel)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ M.cornerKernel) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  obtain ⟨hL, hXY⟩ := M.basic_mod_four
  have hLd : (2 : ℤ) ∣ M.L := Int.dvd_of_emod_eq_zero hL
  have hXY' : M.X % 2 ≠ M.Y % 2 := by omega
  change p ∣ M.cornerClass (false, false) * M.cornerClass (true, false) *
    M.cornerClass (false, true) * M.cornerClass (true, true) at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · exact M.cornerClass_prime_support hLd hXY' (false, false) hp hd
      · exact M.cornerClass_prime_support hLd hXY' (true, false) hp hd
    · exact M.cornerClass_prime_support hLd hXY' (false, true) hp hd
  · exact M.cornerClass_prime_support hLd hXY' (true, true) hp hd

/-- The canonical product has precisely the arithmetic properties required of
 the squarefree kernel in the Gaussian formulation. -/
theorem cornerKernel_properties (M : IntegralModel) (hX : Odd M.X) :
    0 < M.cornerKernel ∧ Odd M.cornerKernel ∧ Squarefree M.cornerKernel ∧
    M.cornerKernel.Coprime M.L.natAbs ∧
    ∀ p : ℕ, p.Prime → p ∣ M.cornerKernel → p % 8 = 1 ∨ p % 8 = 7 :=
  ⟨M.cornerKernel_pos, M.cornerKernel_odd hX, M.cornerKernel_squarefree,
    M.cornerKernel_coprime_side, fun _ hp hd => M.cornerKernel_prime_support hp hd⟩

end FourCorner.IntegralModel

#print axioms FourCorner.IntegralModel.cornerKernel_properties
