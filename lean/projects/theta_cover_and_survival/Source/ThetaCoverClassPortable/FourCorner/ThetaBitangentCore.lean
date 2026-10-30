import Mathlib.Tactic

namespace FourCorner

/-- The literal homogeneous quartic in Section 7. -/
def thetaF {K : Type*} [CommRing K] (x y z : K) : K :=
  9801*(x^4+y^4)+19598*x^2*y^2-39592*(x^2+y^2)*z^2+39984*z^4

/-- Normalized charts covering every projective line in the plane. -/
inductive ThetaLine (K : Type*) where
  | affine (α β : K)
  | vertical (t : K)
  | yzero
  deriving DecidableEq

def ThetaLine.restrict {K : Type*} [CommRing K] (L : ThetaLine K) (x y : K) : K :=
  match L with
  | .affine α β => thetaF x y (α*x+β*y)
  | .vertical t => thetaF (t*x) x y
  | .yzero => thetaF x 0 y

/-- Exact square-factor contact condition on the actual line restriction.
The discriminant excludes a double contact divisor supported at one point. -/
def IsThetaBitangent {K : Type*} [Field K] (L : ThetaLine K) : Prop :=
  ∃ k a b c : K, k≠0 ∧ b^2-4*a*c≠0 ∧
    ∀ x y : K, L.restrict x y = k*(a*x^2+b*x*y+c*y^2)^2

/-- Coefficient form of a nonsingular binary quadratic square. -/
def ThetaSquareCoefficients {K : Type*} [Field K] (A4 A3 A2 A1 A0 : K) : Prop :=
  ∃ k a b c : K, k≠0 ∧ b^2-4*a*c≠0 ∧
    A4=k*a^2 ∧ A3=2*k*a*b ∧ A2=k*(b^2+2*a*c) ∧
    A1=2*k*b*c ∧ A0=k*c^2

def thetaBinaryQuartic {K : Type*} [CommRing K] (A4 A3 A2 A1 A0 x y : K) : K :=
  A4*x^4+A3*x^3*y+A2*x^2*y^2+A1*x*y^3+A0*y^4

def thetaA4 {K : Type*} [CommRing K] (α β : K) : K := 9801-39592*α^2+39984*α^4
def thetaA3 {K : Type*} [CommRing K] (α β : K) : K := 2*α*β*(-39592+79968*α^2)
def thetaA2 {K : Type*} [CommRing K] (α β : K) : K :=
  19598-39592*(α^2+β^2)+239904*α^2*β^2
def thetaA1 {K : Type*} [CommRing K] (α β : K) : K := 2*α*β*(-39592+79968*β^2)
def thetaA0 {K : Type*} [CommRing K] (α β : K) : K := 9801-39592*β^2+39984*β^4

theorem theta_affine_expansion {K : Type*} [CommRing K] (α β x y : K) :
    thetaF x y (α*x+β*y) =
    thetaBinaryQuartic (thetaA4 α β) (thetaA3 α β) (thetaA2 α β)
      (thetaA1 α β) (thetaA0 α β) x y := by
  unfold thetaF thetaBinaryQuartic thetaA4 thetaA3 thetaA2 thetaA1 thetaA0
  ring

theorem theta_vertical_expansion {K : Type*} [CommRing K] (t x y : K) :
    thetaF (t*x) x y =
    thetaBinaryQuartic (9801*(t^4+1)+19598*t^2) 0 (-39592*(t^2+1)) 0 39984 x y := by
  unfold thetaF thetaBinaryQuartic
  ring

theorem theta_yzero_expansion {K : Type*} [CommRing K] (x y : K) :
    thetaF x 0 y = thetaBinaryQuartic 9801 0 (-39592) 0 39984 x y := by
  unfold thetaF thetaBinaryQuartic
  ring

/-- Coefficients are recovered from the actual binary polynomial identity;
five evaluations suffice in characteristic zero. -/
theorem theta_square_coefficients_iff {K : Type*} [Field K] [CharZero K]
    (A4 A3 A2 A1 A0 : K) :
    ThetaSquareCoefficients A4 A3 A2 A1 A0 ↔
    ∃ k a b c : K, k≠0 ∧ b^2-4*a*c≠0 ∧
      ∀ x y : K, thetaBinaryQuartic A4 A3 A2 A1 A0 x y =
        k*(a*x^2+b*x*y+c*y^2)^2 := by
  constructor
  · rintro ⟨k,a,b,c,hk,hd,h4,h3,h2,h1,h0⟩
    refine ⟨k,a,b,c,hk,hd,?_⟩
    intro x y
    rw [thetaBinaryQuartic,h4,h3,h2,h1,h0]
    ring
  · rintro ⟨k,a,b,c,hk,hd,he⟩
    have e0 := he 0 1
    have e1 := he 1 1
    have em1 := he (-1) 1
    have e2 := he 2 1
    have em2 := he (-2) 1
    simp only [thetaBinaryQuartic] at e0 e1 em1 e2 em2
    refine ⟨k,a,b,c,hk,hd,?_,?_,?_,?_,?_⟩
    · linear_combination (1/24:K)*e2+(1/24:K)*em2-(1/6:K)*e1-(1/6:K)*em1+(1/4:K)*e0
    · linear_combination (1/12:K)*e2-(1/12:K)*em2-(1/6:K)*e1+(1/6:K)*em1
    · linear_combination -(1/24:K)*e2-(1/24:K)*em2+(2/3:K)*e1+(2/3:K)*em1-(5/4:K)*e0
    · linear_combination -(1/12:K)*e2+(1/12:K)*em2+(2/3:K)*e1-(2/3:K)*em1
    · linear_combination e0

theorem theta_affine_bitangent_iff {K : Type*} [Field K] [CharZero K] (α β : K) :
    IsThetaBitangent (.affine α β) ↔
    ThetaSquareCoefficients (thetaA4 α β) (thetaA3 α β) (thetaA2 α β)
      (thetaA1 α β) (thetaA0 α β) := by
  rw [theta_square_coefficients_iff]
  simp only [IsThetaBitangent,ThetaLine.restrict,theta_affine_expansion]

theorem theta_vertical_bitangent_iff {K : Type*} [Field K] [CharZero K] (t : K) :
    IsThetaBitangent (.vertical t) ↔
    ThetaSquareCoefficients (9801*(t^4+1)+19598*t^2) 0 (-39592*(t^2+1)) 0 39984 := by
  rw [theta_square_coefficients_iff]
  simp only [IsThetaBitangent,ThetaLine.restrict,theta_vertical_expansion]

theorem theta_yzero_bitangent_iff {K : Type*} [Field K] [CharZero K] :
    IsThetaBitangent (ThetaLine.yzero : ThetaLine K) ↔
    ThetaSquareCoefficients 9801 0 (-39592:K) 0 39984 := by
  rw [theta_square_coefficients_iff]
  simp only [IsThetaBitangent,ThetaLine.restrict,theta_yzero_expansion]

#print axioms theta_square_coefficients_iff
#print axioms theta_affine_bitangent_iff
#print axioms theta_vertical_bitangent_iff
#print axioms theta_yzero_bitangent_iff
end FourCorner
