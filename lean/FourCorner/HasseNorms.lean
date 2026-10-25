import FourCorner.HasseInertNorm
import FourCorner.HasseUnitBranches
import FourCorner.SqrtTwoGlobalNorm
import FourCorner.SqrtTwoFieldNorm
namespace FourCorner.HasseNorms
open HasseNormWitness

/-- The actual finite-rho nonzero four-square source in §05, over a field. -/
structure LocalPoint (K : Type*) [Field K] (p : K) where
  rho : K
  u : K
  v : K
  w : K
  t : K
  rho_ne_zero : rho ≠ 0
  rho_ne_one : rho ≠ 1
  rho_ne_neg_one : rho ≠ -1
  u_ne_zero : u ≠ 0
  v_ne_zero : v ≠ 0
  w_ne_zero : w ≠ 0
  t_ne_zero : t ≠ 0
  sqU : u^2=p*rho
  sqV : v^2=2*(p-1)*(rho-1)
  sqW : w^2=2*(p+1)*(rho+1)
  sqT : t^2=(p-1)*rho+p+1

/-- Paper Loc(p): all four expressions are simultaneous nonzero squares at
a finite rho outside 0,1,-1 over every completion of Q. -/
def Loc (p : ℚ) : Prop :=
  Nonempty (LocalPoint ℝ (p : ℝ)) ∧
  ∀ (q : ℕ) [Fact q.Prime], Nonempty (LocalPoint ℚ_[q] (p : ℚ_[q]))

/-- The arithmetic domain from eq:hp-domain, retained verbatim in the final theorem. -/
def Domain (p : ℚ) : Prop :=
  ∃ n : ℕ, 1<n ∧ Odd n ∧ Squarefree n ∧
    ∃ k : ℚ, k ≠ 0 ∧ p*(p^2-1)=(n : ℚ)*k^2

theorem local_full_equations {K : Type*} [Field K] (p : K) (S : LocalPoint K p) :
    p*S.v^2=2*(p-1)*(S.u^2-p*1^2) ∧
    p*S.w^2=2*(p+1)*(S.u^2+p*1^2) ∧
    p*S.t^2=(p-1)*S.u^2+p*(p+1)*1^2 := by
  rw [S.sqU,S.sqV,S.sqW,S.sqT]
  constructor
  · ring
  constructor <;> ring

theorem local_inert_parities (p : ℚ) (hp : 1<p) (hL : Loc p)
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (h2 : ¬ IsSquare (2 : ℚ_[q])) :
    Even (padicValRat q p) ∧ Even (padicValRat q (p-1)) ∧
    Even (padicValRat q (p+1)) := by
  obtain ⟨S⟩ := hL.2 q
  have hp0 : (p : ℚ_[q]) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  have ha0 : (p : ℚ_[q])-1 ≠ 0 := by exact_mod_cast (show p-1 ≠ 0 by linarith)
  have hb0 : (p : ℚ_[q])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  obtain ⟨hV,hW,hT⟩ := local_full_equations (p : ℚ_[q]) S
  have hh := HasseInertNorm.full_source_inert_valuations hq h2 (p : ℚ_[q]) 1
    S.u S.v S.w S.t hp0 ha0 hb0
    (by rintro ⟨hz,_⟩; exact one_ne_zero hz) hV hW hT
  have hca : ((p-1 : ℚ) : ℚ_[q])=(p : ℚ_[q])-1 := by simp
  have hcb : ((p+1 : ℚ) : ℚ_[q])=(p : ℚ_[q])+1 := by simp
  rcases hh with ⟨hvp,hva,hvb⟩
  rw [← hca,Padic.valuation_ratCast] at hva
  rw [← hcb,Padic.valuation_ratCast] at hvb
  exact ⟨by simpa only [Padic.valuation_ratCast] using hvp,hva,hvb⟩

/-- All three global field norm values follow from Loc, with the global
step supplied by explicit Euclidean prime factorization rather than reciprocity. -/
theorem global_norm_witnesses (p : ℚ) (hp : 1<p) (hL : Loc p) :
    (∃ x : SqrtTwo ℚ, x.norm=p) ∧
    (∃ x : SqrtTwo ℚ, x.norm=p-1) ∧
    (∃ x : SqrtTwo ℚ, x.norm=p+1) := by
  have he (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hns : ¬ IsSquare (2 : ZMod q)) :
      Even (padicValRat q p) ∧ Even (padicValRat q (p-1)) ∧
      Even (padicValRat q (p+1)) := by
    letI : Fact q.Prime := ⟨hq⟩
    exact local_inert_parities p hp hL q hq2 (SqrtTwoGlobalNorm.nonsquare_two_completion hns)
  refine ⟨SqrtTwoGlobalNorm.positive_rat_norm_of_even_inert p (by linarith) ?_,
    SqrtTwoGlobalNorm.positive_rat_norm_of_even_inert (p-1) (by linarith) ?_,
    SqrtTwoGlobalNorm.positive_rat_norm_of_even_inert (p+1) (by linarith) ?_⟩
  · intro q hq hq2 hns; exact (he q hq hq2 hns).1
  · intro q hq hq2 hns; exact (he q hq hq2 hns).2.1
  · intro q hq hq2 hns; exact (he q hq hq2 hns).2.2

theorem norm_at_completion (r : ℚ) (h : ∃ x : SqrtTwo ℚ, x.norm=r)
    (q : ℕ) [Fact q.Prime] : ∃ x : SqrtTwo ℚ_[q], x.norm=(r : ℚ_[q]) := by
  obtain ⟨x,hx⟩ := h
  refine ⟨⟨(x.re : ℚ_[q]),(x.im : ℚ_[q])⟩,?_⟩
  simp only [QuadraticAlgebra.norm_def] at hx ⊢
  exact_mod_cast hx

/-- The exact dyadic conclusion, expressed by actual valuation, integral
congruence and square-ratio statements in Q2. -/
def DyadicConclusion (p : ℚ) : Prop :=
  (4 ≤ (p : ℚ_[2]).valuation ∧ Even (p : ℚ_[2]).valuation) ∨
  ((p : ℚ_[2]).valuation ≤ -4 ∧ Even (p : ℚ_[2]).valuation) ∨
  (∃ P : ℤ_[2], (P : ℚ_[2])=(p : ℚ_[2]) ∧ PadicInt.toZModPow 4 P=1 ∧
    IsSquare (((p : ℚ_[2])-1)/2) ∧ Odd ((p : ℚ_[2])-1).valuation ∧
    5 ≤ ((p : ℚ_[2])-1).valuation) ∨
  (∃ P : ℤ_[2], (P : ℚ_[2])=(p : ℚ_[2]) ∧ PadicInt.toZModPow 4 P=15 ∧
    IsSquare (((p : ℚ_[2])+1)/2) ∧ Odd ((p : ℚ_[2])+1).valuation ∧
    5 ≤ ((p : ℚ_[2])+1).valuation)

theorem dyadic_conclusion (p : ℚ) (hp : 1<p) (hL : Loc p) : DyadicConclusion p := by
  obtain ⟨S⟩ := hL.2 2
  have hp0 : (p : ℚ_[2]) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  have ha0 : (p : ℚ_[2])-1 ≠ 0 := by exact_mod_cast (show p-1 ≠ 0 by linarith)
  have hb0 : (p : ℚ_[2])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hc0 : S.rho-1 ≠ 0 := sub_ne_zero.mpr S.rho_ne_one
  have hd0 : S.rho+1 ≠ 0 := by intro hh; exact S.rho_ne_neg_one (by linear_combination hh)
  have h0 : IsSquare ((p : ℚ_[2])*S.rho) := by rw [← S.sqU]; exact IsSquare.sq _
  have h1 : IsSquare (2*((p : ℚ_[2])-1)*(S.rho-1)) := by rw [← S.sqV]; exact IsSquare.sq _
  have h2 : IsSquare (2*((p : ℚ_[2])+1)*(S.rho+1)) := by rw [← S.sqW]; exact IsSquare.sq _
  have h3 : IsSquare (((p : ℚ_[2])-1)*S.rho+(p : ℚ_[2])+1) := by rw [← S.sqT]; exact IsSquare.sq _
  obtain ⟨hpN,haN,hbN⟩ := global_norm_witnesses p hp hL
  have hpN2 := norm_at_completion p hpN 2
  have haN2 : ∃ x : SqrtTwo ℚ_[2], x.norm=(p : ℚ_[2])-1 := by simpa using norm_at_completion (p-1) haN 2
  have hbN2 : ∃ x : SqrtTwo ℚ_[2], x.norm=(p : ℚ_[2])+1 := by simpa using norm_at_completion (p+1) hbN 2
  rcases HasseDyadicBranches.four_branches (p : ℚ_[2]) S.rho hp0 S.rho_ne_zero
    ha0 hb0 hc0 hd0 h0 h1 h2 h3 hpN2 haN2 hbN2 with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨P,hP,hres⟩ := h
    have hh := HasseUnitBranches.unit_one_branch P S.rho (hP.symm ▸ hp0) S.rho_ne_zero
      (hP.symm ▸ ha0) (hP.symm ▸ hb0) hc0 hd0 (hP.symm ▸ h0) (hP.symm ▸ h1)
      (hP.symm ▸ h2) (hP.symm ▸ h3) hres
    rw [hP] at hh
    exact Or.inr (Or.inr (Or.inl ⟨P,hP,hres,hh⟩))
  · obtain ⟨P,hP,hres⟩ := h
    have hh := HasseUnitBranches.unit_fifteen_branch P S.rho (hP.symm ▸ hp0) S.rho_ne_zero
      (hP.symm ▸ ha0) (hP.symm ▸ hb0) hc0 hd0 (hP.symm ▸ h0) (hP.symm ▸ h1)
      (hP.symm ▸ h2) (hP.symm ▸ h3) hres
    rw [hP] at hh
    exact Or.inr (Or.inr (Or.inr ⟨P,hP,hres,hh⟩))

/-- Full lem:hp-norms. Every norm here is Algebra.norm on the actual quadratic
field Q(√2), whose irreducibility and determinant norm were proved above. -/
theorem hp_norms (p : ℚ) (hp : 1<p) (hL : Loc p) :
    ((∃ x : SqrtTwo ℚ, Algebra.norm ℚ x=p) ∧
     (∃ x : SqrtTwo ℚ, Algebra.norm ℚ x=p-1) ∧
     (∃ x : SqrtTwo ℚ, Algebra.norm ℚ x=p+1)) ∧
    (∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ¬ IsSquare (2 : ℚ_[q]) →
      Even (padicValRat q p) ∧ Even (padicValRat q (p-1)) ∧ Even (padicValRat q (p+1))) ∧
    (Domain p → DyadicConclusion p) := by
  obtain ⟨hpN,haN,hbN⟩ := global_norm_witnesses p hp hL
  refine ⟨⟨SqrtTwoFieldNorm.exists_field_norm p hpN,
    SqrtTwoFieldNorm.exists_field_norm (p-1) haN,SqrtTwoFieldNorm.exists_field_norm (p+1) hbN⟩,?_,?_⟩
  · intro q _ hq hns
    exact local_inert_parities p hp hL q hq hns
  · intro _
    exact dyadic_conclusion p hp hL
#print axioms global_norm_witnesses
#print axioms dyadic_conclusion
#print axioms hp_norms
end FourCorner.HasseNorms
