import ThetaBitangentCore
namespace FourCorner
variable {K : Type*} [Field K]
/-- The actual linear equation attached to each normalized projective line chart. -/
def ThetaLine.equation (L : ThetaLine K) (x y z : K) : K :=
  match L with
  | .affine α β => z-α*x-β*y
  | .vertical t => x-t*y
  | .yzero => y

/-- Every nonzero homogeneous linear form is a nonzero scalar times one and only
one of the normalized chart shapes (existence part). -/
theorem theta_projective_line_chart_cover (A B C : K)
    (hne : A≠0 ∨ B≠0 ∨ C≠0) :
    ∃ L : ThetaLine K, ∃ scalar : K, scalar≠0 ∧
      ∀ x y z : K, A*x+B*y+C*z=scalar*L.equation x y z := by
  by_cases hc : C=0
  · by_cases ha : A=0
    · have hb : B≠0 := by rcases hne with h | h | h; exact (h ha).elim; exact h; exact (h hc).elim
      refine ⟨.yzero,B,hb,?_⟩
      intro x y z
      simp [ThetaLine.equation,ha,hc]
    · refine ⟨.vertical (-B/A),A,ha,?_⟩
      intro x y z
      dsimp [ThetaLine.equation]
      rw [hc]
      field_simp
      ring
  · refine ⟨.affine (-A/C) (-B/C),C,hc,?_⟩
    intro x y z
    dsimp [ThetaLine.equation]
    field_simp
    ring

/-- Each chart restriction parametrizes exactly points on the literal linear equation. -/
theorem theta_chart_parametrizations (L : ThetaLine K) :
    match L with
    | .affine α β => ∀ x y, L.equation x y (α*x+β*y)=0
    | .vertical t => ∀ y z, L.equation (t*y) y z=0
    | .yzero => ∀ x z, L.equation x 0 z=0 := by
  cases L <;> intros <;> simp [ThetaLine.equation] <;> ring

#print axioms theta_projective_line_chart_cover
/-- Distinct normalized chart values are distinct actual projective lines. -/
theorem theta_projective_line_chart_unique (L M : ThetaLine K) (scalar : K)
    (hs : scalar ≠ 0)
    (h : ∀ x y z : K, L.equation x y z=scalar*M.equation x y z) : L=M := by
  have hx := h 1 0 0
  have hy := h 0 1 0
  have hz := h 0 0 1
  clear h
  cases L with
  | affine α β =>
    cases M with
    | affine a b =>
      have he : scalar=1 := by simpa [ThetaLine.equation] using hz.symm
      subst scalar
      have ha : α=a := by simpa [ThetaLine.equation] using hx
      have hb : β=b := by simpa [ThetaLine.equation] using hy
      rw [ha,hb]
    | vertical t => simp [ThetaLine.equation] at hz
    | yzero => simp [ThetaLine.equation] at hz
  | vertical t =>
    cases M with
    | affine a b =>
      have he : scalar=0 := by simpa [ThetaLine.equation] using hz.symm
      exact (hs he).elim
    | vertical u =>
      have he : scalar=1 := by simpa [ThetaLine.equation] using hx.symm
      subst scalar
      have ht : t=u := by simpa [ThetaLine.equation] using hy
      rw [ht]
    | yzero => simp [ThetaLine.equation] at hx
  | yzero =>
    cases M with
    | affine a b =>
      have he : scalar=0 := by simpa [ThetaLine.equation] using hz.symm
      exact (hs he).elim
    | vertical t =>
      have he : scalar=0 := by simpa [ThetaLine.equation] using hx.symm
      exact (hs he).elim
    | yzero => rfl

#print axioms theta_projective_line_chart_unique
end FourCorner
