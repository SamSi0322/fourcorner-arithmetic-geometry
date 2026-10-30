import ThetaBitangentCore
import ThetaBitangentGeneric
import ThetaBitangentCases
import ThetaBitangentAxes
import ThetaBitangentContacts
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace FourCorner

/-- Square contact allowing a double root (potential hyperflex). -/
def ThetaBroadSquare {K : Type*} [Field K] (A4 A3 A2 A1 A0 : K) : Prop :=
  ∃ k a b c : K, k≠0 ∧
    A4=k*a^2 ∧ A3=2*k*a*b ∧ A2=k*(b^2+2*a*c) ∧
    A1=2*k*b*c ∧ A0=k*c^2


variable {K : Type*} [Field K] [CharZero K]

/-- A square restriction with both line coefficients nonzero cannot have its
cubic coefficient zero; this includes potential vanishing endpoint cases. -/
theorem theta_broad_generic_cubic_nonzero {α β : K}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : ThetaBroadSquare (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β)) :
    -39592 + 79968*α^2 ≠ 0 := by
  obtain ⟨k,a,b,c,hk,h4,h3,h2,h1,h0⟩ := h
  intro hg
  have hs : α^2 = (101 : K)/204 := by linear_combination (1/79968 : K)*hg
  have h4val : thetaA4 α β = (2 : K)/51 := by
    unfold thetaA4
    rw [show α^4 = (α^2)^2 by ring, hs]
    norm_num
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide),mul_zero,h4val] at h4
    norm_num at h4
  have hb : b = 0 := by
    have he : (2*k*a)*b = 0 := by rw [← h3]; simp [thetaA3,hg]
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hk) ha)
  have heβ : (2*α*β)*(-39592+79968*β^2) = 0 := by
    simpa only [thetaA1,hb,mul_zero,zero_mul] using h1
  have hgβ : -39592+79968*β^2 = 0 :=
    (mul_eq_zero.mp heβ).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hα) hβ)
  have ht : β^2 = (101 : K)/204 := by linear_combination (1/79968 : K)*hgβ
  have h0val : thetaA0 α β = (2 : K)/51 := by
    unfold thetaA0
    rw [show β^4 = (β^2)^2 by ring, ht]
    norm_num
  have h2val : thetaA2 α β = (1999196 : K)/51 := by
    unfold thetaA2
    rw [hs,ht]
    norm_num
  have he : (thetaA2 α β)^2 = 4*(thetaA4 α β)*(thetaA0 α β) := by
    rw [h2,h4,h0,hb]
    ring
  rw [h4val,h0val,h2val] at he
  norm_num at he

/-- The two square-quartic elimination identities hold without an assumption
that either endpoint or either odd coefficient is nonzero. -/
theorem theta_broad_generic_invariants {α β : K}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : ThetaBroadSquare (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β)) :
    thetaBitangentI (α^2) (β^2) = 0 ∧ thetaBitangentII (α^2) (β^2) = 0 := by
  obtain ⟨k,a,b,c,hk,h4,h3,h2,h1,h0⟩ := h
  have hi : (thetaA3 α β)^2*(thetaA0 α β) -
      (thetaA1 α β)^2*(thetaA4 α β) = 0 := by
    rw [h3,h0,h1,h4]
    ring
  have hii : (thetaA3 α β)^3 - 4*(thetaA4 α β)*(thetaA3 α β)*(thetaA2 α β) +
      8*(thetaA4 α β)^2*(thetaA1 α β) = 0 := by
    rw [h3,h4,h2,h1]
    ring
  have hc : 2*α*β ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hα) hβ
  constructor
  · have he : (thetaA3 α β)^2*(thetaA0 α β) -
        (thetaA1 α β)^2*(thetaA4 α β) =
        (2*α*β)^2 * thetaBitangentI (α^2) (β^2) := by
      unfold thetaA3 thetaA0 thetaA1 thetaA4 thetaBitangentI thetaBitangentF thetaBitangentG
      ring
    rw [he] at hi
    exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero 2 hc)
  · have he : (thetaA3 α β)^3 - 4*(thetaA4 α β)*(thetaA3 α β)*(thetaA2 α β) +
        8*(thetaA4 α β)^2*(thetaA1 α β) =
        (2*α*β) * thetaBitangentII (α^2) (β^2) := by
      unfold thetaA3 thetaA4 thetaA2 thetaA1 thetaBitangentII
        thetaBitangentF thetaBitangentG thetaBitangentH
      ring
    rw [he] at hii
    exact (mul_eq_zero.mp hii).resolve_left hc

/-- Complete necessity for the chart with two nonzero line coefficients. -/
theorem theta_broad_generic_four_cases {α β : K}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : ThetaBroadSquare (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β)) :
    (α^2 = 81/196 ∧ β^2 = 81/196) ∨
    (α^2 = 121/196 ∧ β^2 = 121/196) ∨
    (α^2 = 27/68 ∧ β^2 = 121/204) ∨
    (α^2 = 121/204 ∧ β^2 = 27/68) := by
  have hg : thetaBitangentG (α^2) ≠ 0 := theta_broad_generic_cubic_nonzero hα hβ h
  obtain ⟨hi,hii⟩ := theta_broad_generic_invariants hα hβ h
  exact thetaBitangent_equations_four_cases hi hii hg

#print axioms theta_broad_generic_cubic_nonzero
#print axioms theta_broad_generic_invariants
#print axioms theta_broad_generic_four_cases
/-- A square's binary quartic invariant is exactly its quadratic discriminant squared. -/
theorem theta_broad_invariant (k a b c : K) :
    (k*(b^2+2*a*c))^2 - 3*(2*k*a*b)*(2*k*b*c) +
      12*(k*a^2)*(k*c^2) = k^2*(b^2-4*a*c)^2 := by ring

/-- All generic square contacts are separable; potential hyperflexes were included. -/
theorem theta_broad_generic_separable {α β : K}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : ThetaBroadSquare (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β)) :
    ThetaSquareCoefficients (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β) := by
  have cases := theta_broad_generic_four_cases hα hβ h
  obtain ⟨k,a,b,c,hk,h4,h3,h2,h1,h0⟩ := h
  refine ⟨k,a,b,c,hk,?_,h4,h3,h2,h1,h0⟩
  intro hd
  have hi : (thetaA2 α β)^2 - 3*(thetaA3 α β)*(thetaA1 α β) +
      12*(thetaA4 α β)*(thetaA0 α β) = 0 := by
    rw [h2,h3,h1,h4,h0,theta_broad_invariant,hd]
    ring
  have expr : (thetaA2 α β)^2 - 3*(thetaA3 α β)*(thetaA1 α β) +
      12*(thetaA4 α β)*(thetaA0 α β) =
      (thetaBitangentH (α^2) (β^2))^2 -
      12*(α^2)*(β^2)*(thetaBitangentG (α^2))*(thetaBitangentG (β^2)) +
      12*(thetaBitangentF (α^2))*(thetaBitangentF (β^2)) := by
    unfold thetaA2 thetaA3 thetaA1 thetaA4 thetaA0 thetaBitangentH thetaBitangentG thetaBitangentF
    ring
  rw [expr] at hi
  rcases cases with ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩ <;>
    norm_num [hu,hv,thetaBitangentH,thetaBitangentG,thetaBitangentF] at hi

#print axioms theta_broad_generic_separable
theorem theta_broad_even_relation {A4 A2 A0 : K} (hc0 : A0 ≠ 0)
    (h : ThetaBroadSquare A4 0 A2 0 A0) : A2^2 = 4*A4*A0 := by
  obtain ⟨k,a,b,c,hk,h4,h3,h2,h1,h0⟩ := h
  have hc : c ≠ 0 := by intro hz; apply hc0; simpa [hz] using h0
  have hb : b = 0 := by
    have he : (2*k*b)*c = 0 := h1.symm
    have he' := (mul_eq_zero.mp he).resolve_right hc
    exact (mul_eq_zero.mp he').resolve_left (mul_ne_zero (by norm_num) hk)
  rw [h2,h4,h0,hb]
  ring

theorem theta_broad_even_upgrade {A4 A2 A0 : K} (hc0 : A0 ≠ 0)
    (hm : A2 ≠ 0) (h : ThetaBroadSquare A4 0 A2 0 A0) :
    ThetaSquareCoefficients A4 0 A2 0 A0 :=
  (theta_even_square_iff hc0).mpr ⟨hm,theta_broad_even_relation hc0 h⟩

theorem theta_broad_axis_upgrade (u : K)
    (h : ThetaBroadSquare (9801-39592*u^2+39984*u^4) 0
      (19598-39592*u^2) 0 9801) :
    ThetaSquareCoefficients (9801-39592*u^2+39984*u^4) 0
      (19598-39592*u^2) 0 9801 := by
  have hd := theta_broad_even_relation (by norm_num : (9801:K) ≠ 0) h
  have hu : u^2=1/2 ∨ u^2=50 := by
    apply theta_axis_square_values
    linear_combination hd
  apply theta_broad_even_upgrade (by norm_num) _ h
  rcases hu with hu | hu <;> rw [hu] <;> norm_num

theorem theta_broad_vertical_upgrade (t : K)
    (h : ThetaBroadSquare (9801*(t^4+1)+19598*t^2) 0
      (-39592*(t^2+1)) 0 39984) :
    ThetaSquareCoefficients (9801*(t^4+1)+19598*t^2) 0
      (-39592*(t^2+1)) 0 39984 := by
  have hd := theta_broad_even_relation (by norm_num : (39984:K) ≠ 0) h
  have ht : t^4-100*t^2+1=0 := by
    apply theta_vertical_square_values
    linear_combination hd
  exact (theta_vertical_coefficients_iff t).mpr ht

theorem theta_broad_reverse {A4 A3 A2 A1 A0 : K}
    (h : ThetaBroadSquare A4 A3 A2 A1 A0) :
    ThetaBroadSquare A0 A1 A2 A3 A4 := by
  obtain ⟨k,a,b,c,hk,h4,h3,h2,h1,h0⟩ := h
  refine ⟨k,c,b,a,hk,h0,?_,?_,?_,h4⟩
  · rw [h1]; ring
  · rw [h2]; ring
  · rw [h3]; ring

/-- Every affine square restriction is separable, including both axis charts. -/
theorem theta_broad_affine_upgrade (α β : K)
    (h : ThetaBroadSquare (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β)) :
    ThetaSquareCoefficients (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β) := by
  by_cases ha : α = 0
  · subst α
    apply theta_square_coefficients_reverse
    simpa [thetaA4,thetaA3,thetaA2,thetaA1,thetaA0] using
      theta_broad_axis_upgrade β (by simpa [thetaA4,thetaA3,thetaA2,thetaA1,thetaA0] using theta_broad_reverse h)
  · by_cases hb : β = 0
    · subst β
      simpa [thetaA4,thetaA3,thetaA2,thetaA1,thetaA0] using
        theta_broad_axis_upgrade α (by simpa [thetaA4,thetaA3,thetaA2,thetaA1,thetaA0] using h)
    · exact theta_broad_generic_separable ha hb h

#print axioms theta_broad_affine_upgrade
#print axioms theta_broad_vertical_upgrade
theorem theta_broad_coefficients_iff {K : Type*} [Field K] [CharZero K]
    (A4 A3 A2 A1 A0 : K) :
    ThetaBroadSquare A4 A3 A2 A1 A0 ↔
    ∃ k a b c : K, k≠0 ∧
      ∀ x y : K, thetaBinaryQuartic A4 A3 A2 A1 A0 x y =
        k*(a*x^2+b*x*y+c*y^2)^2 := by
  constructor
  · rintro ⟨k,a,b,c,hk,h4,h3,h2,h1,h0⟩
    refine ⟨k,a,b,c,hk,?_⟩
    intro x y
    rw [thetaBinaryQuartic,h4,h3,h2,h1,h0]
    ring
  · rintro ⟨k,a,b,c,hk,he⟩
    have e0 := he 0 1
    have e1 := he 1 1
    have em1 := he (-1) 1
    have e2 := he 2 1
    have em2 := he (-2) 1
    simp only [thetaBinaryQuartic] at e0 e1 em1 e2 em2
    refine ⟨k,a,b,c,hk,?_,?_,?_,?_,?_⟩
    · linear_combination (1/24:K)*e2+(1/24:K)*em2-(1/6:K)*e1-(1/6:K)*em1+(1/4:K)*e0
    · linear_combination (1/12:K)*e2-(1/12:K)*em2-(1/6:K)*e1+(1/6:K)*em1
    · linear_combination -(1/24:K)*e2-(1/24:K)*em2+(2/3:K)*e1+(2/3:K)*em1-(5/4:K)*e0
    · linear_combination -(1/12:K)*e2+(1/12:K)*em2+(2/3:K)*e1-(2/3:K)*em1
    · linear_combination e0

/-- Square contact without a separability assumption, on the literal quartic. -/
def IsThetaSquareContact (L : ThetaLine K) : Prop :=
  ∃ k a b c : K, k≠0 ∧ ∀ x y : K,
    L.restrict x y = k*(a*x^2+b*x*y+c*y^2)^2

/-- Exhaustive no-hyperflex result in every normalized projective line chart. -/
theorem theta_no_hyperflex (L : ThetaLine K) :
    IsThetaSquareContact L ↔ IsThetaBitangent L := by
  constructor
  · intro h
    cases L with
    | affine α β =>
      apply (theta_affine_bitangent_iff α β).mpr
      apply theta_broad_affine_upgrade
      apply (theta_broad_coefficients_iff _ _ _ _ _).mpr
      simpa [IsThetaSquareContact,ThetaLine.restrict,theta_affine_expansion] using h
    | vertical t =>
      apply (theta_vertical_bitangent_iff t).mpr
      apply theta_broad_vertical_upgrade
      apply (theta_broad_coefficients_iff _ _ _ _ _).mpr
      simpa [IsThetaSquareContact,ThetaLine.restrict,theta_vertical_expansion] using h
    | yzero =>
      have hb : ThetaBroadSquare 9801 0 (-39592:K) 0 39984 := by
        apply (theta_broad_coefficients_iff _ _ _ _ _).mpr
        simpa [IsThetaSquareContact,ThetaLine.restrict,theta_yzero_expansion] using h
      have he := theta_broad_even_relation (by norm_num : (39984:K) ≠ 0) hb
      norm_num at he
  · rintro ⟨k,a,b,c,hk,hd,he⟩
    exact ⟨k,a,b,c,hk,he⟩

#print axioms theta_no_hyperflex
/-- Complete chartwise necessity, now including all possible square contacts. -/
theorem theta_square_contact_classification (L : ThetaLine K)
    (h : IsThetaSquareContact L) :
    match L with
    | .affine α β =>
      (β=0 ∧ (α^2=1/2 ∨ α^2=50)) ∨
      (α=0 ∧ (β^2=1/2 ∨ β^2=50)) ∨
      (α^2=81/196 ∧ β^2=81/196) ∨
      (α^2=121/196 ∧ β^2=121/196) ∨
      (α^2=27/68 ∧ β^2=121/204) ∨
      (α^2=121/204 ∧ β^2=27/68)
    | .vertical t => t^4-100*t^2+1=0
    | .yzero => False := by
  have hb := (theta_no_hyperflex L).mp h
  cases L with
  | affine α β =>
    by_cases hβ : β=0
    · subst β
      exact Or.inl ⟨rfl,(theta_affine_x_axis_bitangent_iff α).mp hb⟩
    · by_cases hα : α=0
      · subst α
        exact Or.inr (Or.inl ⟨rfl,(theta_affine_y_axis_bitangent_iff β).mp hb⟩)
      · exact Or.inr (Or.inr (theta_bitangent_generic_four_cases hα hβ
          ((theta_affine_bitangent_iff α β).mp hb)))
  | vertical t => exact (theta_vertical_line_bitangent_iff t).mp hb
  | yzero => exact theta_yzero_not_bitangent hb

/-- Separable homogeneous quadratics have two distinct projective zeros.
The nonzero determinant certifies that the two pairs represent distinct points. -/
theorem theta_quadratic_two_points [IsAlgClosed K] (a b c : K)
    (hd : b^2-4*a*c ≠ 0) :
    ∃ x₁ y₁ x₂ y₂ : K, x₁*y₂-x₂*y₁ ≠ 0 ∧
      a*x₁^2+b*x₁*y₁+c*y₁^2=0 ∧
      a*x₂^2+b*x₂*y₂+c*y₂^2=0 := by
  by_cases ha : a=0
  · subst a
    have hb : b ≠ 0 := by intro hz; apply hd; simp [hz]
    refine ⟨1,0,-c,b,?_,?_,?_⟩
    · simpa using hb
    · ring
    · ring
  · obtain ⟨d,hs⟩ := IsAlgClosed.exists_pow_nat_eq (b^2-4*a*c) (by decide : 0<2)
    have hd' : d ≠ 0 := by intro hz; apply hd; simpa [hz] using hs.symm
    refine ⟨-b+d,2*a,-b-d,2*a,?_,?_,?_⟩
    · have he : (-b+d)*(2*a)-(-b-d)*(2*a)=4*a*d := by ring
      rw [he]
      exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hd'
    · linear_combination a*hs
    · linear_combination a*hs

/-- Every square-contact line has two distinct actual homogeneous contact parameters. -/
theorem theta_square_contact_two_points [IsAlgClosed K] (L : ThetaLine K)
    (h : IsThetaSquareContact L) :
    ∃ x₁ y₁ x₂ y₂ : K, x₁*y₂-x₂*y₁ ≠ 0 ∧
      L.restrict x₁ y₁=0 ∧ L.restrict x₂ y₂=0 := by
  obtain ⟨k,a,b,c,hk,hd,he⟩ := (theta_no_hyperflex L).mp h
  obtain ⟨x₁,y₁,x₂,y₂,hn,h₁,h₂⟩ := theta_quadratic_two_points a b c hd
  exact ⟨x₁,y₁,x₂,y₂,hn,by rw [he,h₁]; ring,by rw [he,h₂]; ring⟩

#print axioms theta_square_contact_classification
#print axioms theta_square_contact_two_points
/-- The four displayed line families of Theorem theta-lines, using literal radicals. -/
def ThetaDisplayedLine (r s : K) (L : ThetaLine K) : Prop :=
  (∃ u, (u^2=1/2 ∨ u^2=50) ∧ (L=.affine u 0 ∨ L=.affine 0 u)) ∨
  (∃ ε η, ε^2=1 ∧ η^2=1 ∧
    (L=.affine (9*ε/14) (9*η/14) ∨ L=.affine (11*ε/14) (11*η/14))) ∨
  (∃ ε η, ε^2=1 ∧ η^2=1 ∧
    (L=.affine (s*ε*9/102) (s*η*11/102) ∨
     L=.affine (s*ε*11/102) (s*η*9/102))) ∨
  (∃ ε η, ε^2=1 ∧ η^2=1 ∧ L=.vertical (ε*r*(s+7*η)/2))

lemma theta_eq_sign_mul {u v : K} (h : u^2=v^2) :
    ∃ ε : K, ε^2=1 ∧ u=ε*v := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨1,by norm_num,by simpa using h⟩
  · exact ⟨-1,by norm_num,by simpa using h⟩

lemma theta_vertical_explicit_exhaustive (r s t : K)
    (hr : r^2=2) (hs : s^2=51) (ht : t^4-100*t^2+1=0) :
    ∃ ε η : K, ε^2=1 ∧ η^2=1 ∧ t=ε*r*(s+7*η)/2 := by
  have hv : (t^2-50)^2=(7*s)^2 := by
    linear_combination ht - 49*hs
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hv with hp | hm
  · have ht' : t^2=(r*(s+7)/2)^2 := by
      calc
        _ = 50+7*s := by linear_combination hp
        _ = _ := by rw [div_pow,mul_pow,hr]; linear_combination -(1/2:K)*hs
    obtain ⟨ε,he,hε⟩ := theta_eq_sign_mul ht'
    exact ⟨ε,1,he,by norm_num,by rw [hε]; ring⟩
  · have ht' : t^2=(r*(s-7)/2)^2 := by
      calc
        _ = 50-7*s := by linear_combination hm
        _ = _ := by rw [div_pow,mul_pow,hr]; linear_combination -(1/2:K)*hs
    obtain ⟨ε,he,hε⟩ := theta_eq_sign_mul ht'
    exact ⟨ε,-1,he,by norm_num,by rw [hε]; ring⟩

/-- Complete square-contact exhaustion and sufficiency for all displayed families.
No separability assumption is imposed on the input contact. -/
theorem theta_square_contact_displayed_iff (r s : K) (hr : r^2=2) (hs : s^2=51)
    (L : ThetaLine K) : IsThetaSquareContact L ↔ ThetaDisplayedLine r s L := by
  constructor
  · intro h
    have hc := theta_square_contact_classification L h
    cases L with
    | yzero => exact hc.elim
    | vertical t =>
      obtain ⟨ε,η,he,hh,ht⟩ := theta_vertical_explicit_exhaustive r s t hr hs hc
      exact Or.inr (Or.inr (Or.inr ⟨ε,η,he,hh,by rw [ht]⟩))
    | affine α β =>
      rcases hc with ⟨hβ,hu⟩ | ⟨hα,hu⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩
      · exact Or.inl ⟨α,hu,Or.inl (by rw [hβ])⟩
      · exact Or.inl ⟨β,hu,Or.inr (by rw [hα])⟩
      · obtain ⟨ε,he,hε⟩ := theta_eq_sign_mul (show α^2=(9/14:K)^2 by rw [hu]; norm_num)
        obtain ⟨η,hh,hη⟩ := theta_eq_sign_mul (show β^2=(9/14:K)^2 by rw [hv]; norm_num)
        exact Or.inr (Or.inl ⟨ε,η,he,hh,Or.inl (by rw [hε,hη]; congr 1 <;> ring)⟩)
      · obtain ⟨ε,he,hε⟩ := theta_eq_sign_mul (show α^2=(11/14:K)^2 by rw [hu]; norm_num)
        obtain ⟨η,hh,hη⟩ := theta_eq_sign_mul (show β^2=(11/14:K)^2 by rw [hv]; norm_num)
        exact Or.inr (Or.inl ⟨ε,η,he,hh,Or.inr (by rw [hε,hη]; congr 1 <;> ring)⟩)
      · obtain ⟨ε,he,hε⟩ := theta_eq_sign_mul (show α^2=(s*9/102)^2 by rw [hu]; simp [div_pow,mul_pow,hs]; norm_num)
        obtain ⟨η,hh,hη⟩ := theta_eq_sign_mul (show β^2=(s*11/102)^2 by rw [hv]; simp [div_pow,mul_pow,hs]; norm_num)
        exact Or.inr (Or.inr (Or.inl ⟨ε,η,he,hh,Or.inl (by rw [hε,hη]; congr 1 <;> ring)⟩))
      · obtain ⟨ε,he,hε⟩ := theta_eq_sign_mul (show α^2=(s*11/102)^2 by rw [hu]; simp [div_pow,mul_pow,hs]; norm_num)
        obtain ⟨η,hh,hη⟩ := theta_eq_sign_mul (show β^2=(s*9/102)^2 by rw [hv]; simp [div_pow,mul_pow,hs]; norm_num)
        exact Or.inr (Or.inr (Or.inl ⟨ε,η,he,hh,Or.inr (by rw [hε,hη]; congr 1 <;> ring)⟩))
  · intro h
    apply (theta_no_hyperflex L).mpr
    rcases h with ⟨u,hu,hL | hL⟩ | ⟨ε,η,he,hh,hL | hL⟩ | ⟨ε,η,he,hh,hL | hL⟩ | ⟨ε,η,he,hh,hL⟩
    · rw [hL]; exact (theta_affine_x_axis_bitangent_iff u).mpr hu
    · rw [hL]; exact (theta_affine_y_axis_bitangent_iff u).mpr hu
    · rw [hL]; exact theta_bitangent_II_nine ε η he hh
    · rw [hL]; exact theta_bitangent_II_eleven ε η he hh
    · rw [hL]; exact theta_bitangent_III_nine_eleven s ε η hs he hh
    · rw [hL]; exact theta_bitangent_III_eleven_nine s ε η hs he hh
    · rw [hL]; exact theta_bitangent_IV r s ε η hr hs he hh

/-- The first family's squared parameters are exactly the paper's radical parameters. -/
theorem theta_axis_radical_parameters (r u : K) (hr : r^2=2) :
    (u^2=1/2 ∨ u^2=50) ↔
      ∃ ε : K, ε^2=1 ∧ (u=ε*r/2 ∨ u=5*ε*r) := by
  constructor
  · rintro (h | h)
    · obtain ⟨ε,he,hε⟩ := theta_eq_sign_mul (show u^2=(r/2)^2 by rw [h,div_pow,hr]; norm_num)
      exact ⟨ε,he,Or.inl (by rw [hε]; ring)⟩
    · obtain ⟨ε,he,hε⟩ := theta_eq_sign_mul (show u^2=(5*r)^2 by rw [h,mul_pow,hr]; norm_num)
      exact ⟨ε,he,Or.inr (by rw [hε]; ring)⟩
  · rintro ⟨ε,he,h | h⟩
    · rw [h]; left; rw [div_pow,mul_pow,he,hr]; norm_num
    · rw [h]; right; norm_num [mul_pow,he,hr]

#print axioms theta_square_contact_displayed_iff
#print axioms theta_axis_radical_parameters
end FourCorner
