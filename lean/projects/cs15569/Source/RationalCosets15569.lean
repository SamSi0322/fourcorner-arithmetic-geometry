import HSupport15569
import Cs15569Finite

/-! Exact P/G Kummer rows and complete H image in E(Q)/2E(Q).
The compensator below is an arbitrary rational point, not asserted to lie in H.
Consequently this is not the paper's H/2H or H/8H generation statement. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource OrderedSplit
noncomputable section

abbrev E := CommonSource.Point (15569 : ℚ)
def P : E := finitePoint (by norm_num) Cs15569Finite.p_on_curve
def G : E := finitePoint (by norm_num) Cs15569Finite.g_on_curve
theorem P_depth : padicValRat 2 Cs15569Finite.px = -8 := by
  norm_num [Cs15569Finite.px, padicValRat, padicValInt]
  rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 949405108689),
    show (60217600 : ℕ)=2^8*235225 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num),padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 235225)]
  norm_num

theorem G_depth : padicValRat 2 Cs15569Finite.gx = -6 := by
  norm_num [Cs15569Finite.gx, padicValRat, padicValInt]
  rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 2846726402787145169),
    show (179102547726400 : ℕ)=2^6*2798477308225 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num),padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 2798477308225)]
  norm_num

theorem P_mem_H : P ∈ H 15569 (by norm_num) := by
  rw [P, finitePoint, some_mem_H_iff]
  rw [P_depth]
  norm_num

theorem G_mem_H : G ∈ H 15569 (by norm_num) := by
  rw [G, finitePoint, some_mem_H_iff]
  rw [G_depth]
  norm_num

def N : Units.modPow ℚ 2 := scalarClass (15569 : ℚ) (by norm_num)
def δ : E → Fin 3 → Units.modPow ℚ 2 := fun Q =>
  kummerDelta 15569 (by norm_num) (Multiplicative.ofAdd Q)

theorem N_ne_one : N ≠ 1 := by
  intro hh
  have hs := (scalarClass_eq_one_iff (15569 : ℚ) (by norm_num)).mp hh
  exact Cs15569Finite.n_prime.not_isSquare (Rat.isSquare_natCast_iff.mp hs)

theorem N_mul_N : N*N=1 := by
  unfold N
  rw [scalarClass_mul,scalarClass_eq_one_iff]
  exact ⟨15569,rfl⟩

/-- P=(n,1) in the literal first two ordered descent slots. -/
theorem P_kummer : δ P 0 = N ∧ δ P 1 = 1 := by
  unfold δ P
  rw [kummerDelta_finitePoint _ Cs15569Finite.p_on_curve
    (by norm_num [Cs15569Finite.px]) (by norm_num [Cs15569Finite.px])
    (by norm_num [Cs15569Finite.px])]
  constructor
  · apply scalarClass_eq_of_mul_square (q := (7809/7760 : ℚ))
    norm_num [Cs15569Finite.px]
  · apply (scalarClass_eq_one_iff _ _).mpr
    exact ⟨108983/7760, by simpa [pow_two] using Cs15569Finite.p_factorization.1⟩

/-- G=(n,n) in those same two ordered slots. -/
theorem G_kummer : δ G 0 = N ∧ δ G 1 = N := by
  unfold δ G
  rw [kummerDelta_finitePoint _ Cs15569Finite.g_on_curve
    (by norm_num [Cs15569Finite.gx]) (by norm_num [Cs15569Finite.gx])
    (by norm_num [Cs15569Finite.gx])]
  constructor
  · apply scalarClass_eq_of_mul_square (q := (13522049/13382920 : ℚ))
    norm_num [Cs15569Finite.gx]
  · apply scalarClass_eq_of_mul_square (q := (1934751/13382920 : ℚ))
    exact Cs15569Finite.g_factorization.1

theorem δ_add (Q R : E) : δ (Q+R)=δ Q*δ R := kummerDelta_add _ _ Q R
@[simp] theorem δ_zero : δ 0=1 := kummerDelta_O _ _

theorem GP_kummer : δ (G+P) 0 = 1 ∧ δ (G+P) 1 = N := by
  rw [δ_add]
  constructor
  · change δ G 0 * δ P 0=1
    rw [G_kummer.1,P_kummer.1,N_mul_N]
  · change δ G 1 * δ P 1=N
    rw [G_kummer.2,P_kummer.2,mul_one]

/-- These four actual rational points have pairwise distinct images modulo
2E(Q). This proves independence, and does not assume a rank computation. -/
theorem distinct_kummer_representatives :
    δ 0 ≠ δ P ∧ δ 0 ≠ δ G ∧ δ 0 ≠ δ (G+P) ∧
      δ P ≠ δ G ∧ δ P ≠ δ (G+P) ∧ δ G ≠ δ (G+P) := by
  have h0 : δ (0:E) 0=1 := congrFun δ_zero 0
  have h1 : δ (0:E) 1=1 := congrFun δ_zero 1
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro hh; exact N_ne_one ((P_kummer.1.symm.trans (congrFun hh 0).symm).trans h0)
  · intro hh; exact N_ne_one ((G_kummer.1.symm.trans (congrFun hh 0).symm).trans h0)
  · intro hh; exact N_ne_one ((GP_kummer.2.symm.trans (congrFun hh 1).symm).trans h1)
  · intro hh; exact N_ne_one ((G_kummer.2.symm.trans (congrFun hh 1).symm).trans P_kummer.2)
  · intro hh; exact N_ne_one ((P_kummer.1.symm.trans (congrFun hh 0)).trans GP_kummer.1)
  · intro hh; exact N_ne_one ((G_kummer.1.symm.trans (congrFun hh 0)).trans GP_kummer.1)

private theorem same_two_slots_coset (Q R : E)
    (h0 : δ Q 0=δ R 0) (h1 : δ Q 1=δ R 1) :
    ∃ Z : E, Q=R+2 • Z := by
  apply (kummerDelta_eq_iff_coset 15569 (by norm_num) Q R).mp
  exact (kummerDelta_eq_iff_first_two 15569 (by norm_num) Q R).mpr ⟨h0,h1⟩

/-- Complete, unbounded generation of the image of the actual entire H in
the ambient rational quotient. This does not place Z in H. -/
theorem entire_H_ambient_mod_two (Q : E) (hQ : Q ∈ H 15569 (by norm_num)) :
    (∃ Z : E, Q=2 • Z) ∨
    (∃ Z : E, Q=P+2 • Z) ∨
    (∃ Z : E, Q=G+2 • Z) ∨
    (∃ Z : E, Q=(G+P)+2 • Z) := by
  have hslots := entire_H_kummer_support Q hQ
  rcases hslots 0 with h0 | h0 <;> rcases hslots 1 with h1 | h1
  · left
    obtain ⟨Z,hZ⟩ := same_two_slots_coset Q 0
      (h0.trans (congrFun δ_zero 0).symm) (h1.trans (congrFun δ_zero 1).symm)
    exact ⟨Z,by simpa using hZ⟩
  · right; right; right
    exact same_two_slots_coset Q (G+P) (h0.trans GP_kummer.1.symm) (h1.trans GP_kummer.2.symm)
  · right; left
    exact same_two_slots_coset Q P (h0.trans P_kummer.1.symm) (h1.trans P_kummer.2.symm)
  · right; right; left
    exact same_two_slots_coset Q G (h0.trans G_kummer.1.symm) (h1.trans G_kummer.2.symm)

#print axioms P_mem_H
#print axioms G_mem_H
#print axioms N_ne_one
#print axioms P_kummer
#print axioms G_kummer
#print axioms distinct_kummer_representatives
#print axioms entire_H_ambient_mod_two
end
end FourCorner.Cs15569Completion
