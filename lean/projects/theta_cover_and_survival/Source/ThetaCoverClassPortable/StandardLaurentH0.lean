import ThetaCoverClassPortable.StandardLaurentH1

noncomputable section
open Polynomial LaurentPolynomial
namespace FourCorner.StandardLaurentCech
variable {R : Type*} [CommRing R]

theorem monomial_supported (n : ℤ) (a : R) (s : Set ℤ) (hn : n ∈ s) :
    LaurentPolynomial.C a * T n ∈ AddMonoidAlgebra.supported R R s := by
  rw [AddMonoidAlgebra.mem_supported]
  intro k hk
  have heq : k = n := by simpa using (LaurentPolynomial.support_C_mul_T a n) hk
  simpa only [heq] using hn

theorem range_plus : LinearMap.range (plus (R := R)) =
    AddMonoidAlgebra.supported R R (Set.Ici (0 : ℤ)) := by
  apply le_antisymm
  · rintro z ⟨p, rfl⟩
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using (AddMonoidAlgebra.supported R R _).add_mem hp hq
    | monomial n a =>
      rw [plus_monomial]
      exact monomial_supported _ _ _ (Int.natCast_nonneg n)
  · rw [AddMonoidAlgebra.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro z ⟨n, hn, rfl⟩
    refine ⟨monomial n.toNat 1, ?_⟩
    rw [plus_monomial, Int.toNat_of_nonneg hn, map_one, one_mul]
    rfl

theorem range_minus (d : ℤ) : LinearMap.range (minus (R := R) d) =
    AddMonoidAlgebra.supported R R (Set.Iic d) := by
  apply le_antisymm
  · rintro z ⟨p, rfl⟩
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using (AddMonoidAlgebra.supported R R _).add_mem hp hq
    | monomial n a =>
      rw [minus_monomial]
      exact monomial_supported _ _ _ (sub_le_self d (Int.natCast_nonneg n))
  · rw [AddMonoidAlgebra.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro z ⟨n, hn, rfl⟩
    refine ⟨monomial (d-n).toNat 1, ?_⟩
    rw [minus_monomial, Int.toNat_of_nonneg (sub_nonneg.mpr hn), sub_sub_cancel,
      map_one, one_mul]
    rfl

abbrev H0 (d : ℤ) := LinearMap.ker (differential (R := R) d)
abbrev Common (d : ℤ) := LinearMap.range (minus (R := R) d) ⊓ LinearMap.range plus

theorem restrictions_equal (d : ℤ) (x : H0 (R := R) d) :
    minus d x.1.1 = plus x.1.2 := by
  have h := x.property
  change -(minus d x.1.1) + plus x.1.2 = 0 at h
  exact neg_add_eq_zero.mp h

def h0ToCommon (d : ℤ) : H0 (R := R) d →ₗ[R] Common (R := R) d :=
  LinearMap.codRestrict _
    (plus.comp ((LinearMap.snd R (Polynomial R) (Polynomial R)).comp
      (LinearMap.ker (differential d)).subtype))
    (fun x => ⟨⟨x.1.1, restrictions_equal d x⟩, ⟨x.1.2, rfl⟩⟩)

theorem h0ToCommon_bijective (d : ℤ) : Function.Bijective (h0ToCommon (R := R) d) := by
  constructor
  · intro x y h
    have hq : x.1.2 = y.1.2 := plus_injective (congrArg Subtype.val h)
    have hp : x.1.1 = y.1.1 := minus_injective d
      ((restrictions_equal d x).trans ((congrArg plus hq).trans (restrictions_equal d y).symm))
    apply Subtype.ext
    exact Prod.ext hp hq
  · intro z
    obtain ⟨p, hp⟩ := z.property.1
    obtain ⟨q, hq⟩ := z.property.2
    have hk : (p,q) ∈ LinearMap.ker (differential (R := R) d) := by
      change -(minus d p) + plus q = 0
      rw [hp, hq, neg_add_cancel]
    exact ⟨⟨(p,q), hk⟩, Subtype.ext hq⟩

theorem common_eq_band (d : ℤ) : Common (R := R) d =
    AddMonoidAlgebra.supported R R (Set.Icc 0 d) := by
  rw [Common, range_minus, range_plus]
  ext z
  simp only [Submodule.mem_inf, AddMonoidAlgebra.mem_supported, Set.subset_def,
    Set.mem_Iic, Set.mem_Ici, Set.mem_Icc]
  constructor
  · rintro ⟨hd,h0⟩ n hn
    exact ⟨h0 n hn,hd n hn⟩
  · intro h
    exact ⟨fun n hn => (h n hn).2, fun n hn => (h n hn).1⟩

/-- The actual kernel is finite over every commutative coefficient ring,
including the zero ring. No Noetherian condition is needed for standard twists. -/
theorem finite_H0 (d : ℤ) : Module.Finite R (H0 (R := R) d) := by
  classical
  haveI : Finite (Set.Icc (0 : ℤ) d) := (Set.finite_Icc 0 d).to_subtype
  let e := AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R) (Set.Icc 0 d)
  haveI : Module.Finite R (AddMonoidAlgebra.supported R R (Set.Icc 0 d)) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  let eCommon := LinearEquiv.ofEq (Common (R := R) d) _ (common_eq_band d)
  haveI : Module.Finite R (Common (R := R) d) :=
    Module.Finite.of_surjective eCommon.symm.toLinearMap eCommon.symm.surjective
  let eKernel := LinearEquiv.ofBijective (h0ToCommon (R := R) d) (h0ToCommon_bijective (R := R) d)
  exact Module.Finite.of_surjective eKernel.symm.toLinearMap eKernel.symm.surjective

#print axioms range_plus
#print axioms range_minus
#print axioms h0ToCommon_bijective
#print axioms common_eq_band
#print axioms finite_H0
end FourCorner.StandardLaurentCech
