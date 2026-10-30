import RationalSupport15569
import LocalKummerSelection

/-! The actual whole dyadic subgroup has only {1,15569} in each ordinary
Kummer slot. This is a global descent bridge, not a quotient-generation
hypothesis. In particular it does not assert the missing torsion splitting. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace FourCorner.Cs15569Completion
open CommonSource OrderedSplit

/-- Global support plus an actual dyadic square eliminates all six other
signed classes. Integrality of a square root is proved before reduction. -/
theorem supported_local_square {q : ℚ} (hg : SupportedClass q)
    (hl : IsSquare (q : ℚ_[2])) :
    ∃ d : ℤ, (d = 1 ∨ d = 15569) ∧
      ∃ u : ℚ, 0 < u ∧ q = (d : ℚ)*u^2 := by
  obtain ⟨d,hd,u,hu,he⟩ := hg
  have hun : (u : ℚ_[2]) ≠ 0 := by exact_mod_cast hu.ne'
  have he' : (q : ℚ_[2]) = (d : ℚ_[2])*(u : ℚ_[2])^2 := by exact_mod_cast he
  have hdiv : (q : ℚ_[2])/(u : ℚ_[2])^2 = (d : ℚ_[2]) := by
    rw [he']; field_simp
  have hdlocal : IsSquare (d : ℚ_[2]) := hdiv ▸ hl.div (IsSquare.sq _)
  have hdint : IsSquare (d : ℤ_[2]) := (padicInt_isSquare_coe_iff (d : ℤ_[2])).mp hdlocal
  have hdres : IsSquare (d : ZMod 8) := by
    simpa using hdint.map (PadicInt.toZModPow 3)
  have hdgood : d = 1 ∨ d = 15569 := by
    rcases hd with h | h | h | h | h | h | h | h <;> subst d
    · exact Or.inl rfl
    · exact False.elim ((by decide : ¬ IsSquare (-1 : ZMod 8)) hdres)
    · exact False.elim ((by decide : ¬ IsSquare (2 : ZMod 8)) hdres)
    · exact False.elim ((by decide : ¬ IsSquare (-2 : ZMod 8)) hdres)
    · exact Or.inr rfl
    · exact False.elim ((by decide : ¬ IsSquare (-15569 : ZMod 8)) hdres)
    · exact False.elim ((by decide : ¬ IsSquare (31138 : ZMod 8)) hdres)
    · exact False.elim ((by decide : ¬ IsSquare (-31138 : ZMod 8)) hdres)
  exact ⟨d,hdgood,u,hu,he⟩

theorem first_supported_supported {q : ℚ} (h : FirstSupportedClass q) : SupportedClass q := by
  obtain ⟨d,hd,u,hu,he⟩ := h
  refine ⟨d,?_,u,hu,he⟩
  rcases hd with h | h | h | h <;> simp [h]

/-- Every rational point of depth at least two, at every height, has the
literal ordinary slot classes {1,n}² (and the same conclusion in slot three). -/
theorem depth_two_global_classes {x y : ℚ}
    (h : y^2=x*(x-15569)*(x+15569)) (hv : padicValRat 2 x ≤ -4) :
    (∃ d : ℤ, (d=1 ∨ d=15569) ∧ ∃ u : ℚ, 0<u ∧ x=(d:ℚ)*u^2) ∧
    (∃ d : ℤ, (d=1 ∨ d=15569) ∧ ∃ u : ℚ, 0<u ∧ x-15569=(d:ℚ)*u^2) ∧
    (∃ d : ℤ, (d=1 ∨ d=15569) ∧ ∃ u : ℚ, 0<u ∧ x+15569=(d:ℚ)*u^2) := by
  have hx : x ≠ 0 := by intro hz; simp [hz] at hv
  let chart := commonSourceDyadicOfRat 15569 x y h hv
  have hn : ‖(15569 : ℚ_[2])‖ ≤ 1 := Padic.norm_int_le_one 15569
  have hne := chart.offsets_ne_zero hn
  have hm : x-15569 ≠ 0 := by
    have hh : (x : ℚ_[2])-15569 ≠ 0 := by
      simpa [chart, commonSourceDyadicOfRat] using hne.1
    exact_mod_cast hh
  have hp : x+15569 ≠ 0 := by
    have hh : (x : ℚ_[2])+15569 ≠ 0 := by
      simpa [chart, commonSourceDyadicOfRat] using hne.2
    exact_mod_cast hh
  obtain ⟨hs0,hs1,hs2⟩ := commonSourceDyadic_rational_local_squares 15569 x y h hv
  exact ⟨supported_local_square (first_supported_supported (first_support hx h)) hs0,
    supported_local_square (minus_support hm h) hs1,
    supported_local_square (plus_support hp h) hs2⟩

/-- Every finite H-point lies on the real identity component, beyond +n.
This is deduced from global support and the actual dyadic square test. -/
theorem depth_two_real_identity {x y : ℚ}
    (h : y^2=x*(x-15569)*(x+15569)) (hv : padicValRat 2 x ≤ -4) : 15569 < x := by
  obtain ⟨d,hd,u,hu,he⟩ := (depth_two_global_classes h hv).2.1
  have hpos : 0 < x-15569 := by
    rw [he]
    rcases hd with hd | hd <;> rw [hd] <;> positivity
  linarith

/-- Pointwise actual-group version, including infinity: the full three
ordered Kummer coordinates of every H-point are either 1 or [15569]. -/
theorem entire_H_kummer_support (P : CommonSource.Point (15569 : ℚ))
    (hP : P ∈ H 15569 (by norm_num)) :
    ∀ i : Fin 3, kummerDelta 15569 (by norm_num) (Multiplicative.ofAdd P) i = 1 ∨
      kummerDelta 15569 (by norm_num) (Multiplicative.ofAdd P) i =
        scalarClass (15569 : ℚ) (by norm_num) := by
  cases P with
  | zero =>
    intro i
    left
    have hz := kummerDelta_O 15569 (by norm_num)
    exact congrFun hz i
  | some x y he =>
    have hv := (some_mem_H_iff 15569 (by norm_num) x y he).mp hP
    have hE : CongruentEquation 15569 x y :=
      (congruentEquation_iff_weierstrass _ _ _).mpr he.1
    have hc := depth_two_global_classes hE hv
    have hx : x ≠ 0 := by intro hz; simp [hz] at hv
    have hm : x-15569 ≠ 0 := by
      obtain ⟨d,hd,u,hu,heq⟩ := hc.2.1
      rcases hd with hd | hd <;> rw [heq,hd] <;> positivity
    have hp : x+15569 ≠ 0 := by
      obtain ⟨d,hd,u,hu,heq⟩ := hc.2.2
      rcases hd with hd | hd <;> rw [heq,hd] <;> positivity
    have hfinite : (.some x y he : CommonSource.Point 15569) = finitePoint (by norm_num) hE := rfl
    rw [hfinite,kummerDelta_finitePoint _ hE hx hm hp]
    intro i
    have helper : ∀ {q : ℚ} (hq : q ≠ 0),
        (∃ d : ℤ, (d=1 ∨ d=15569) ∧ ∃ u : ℚ, 0<u ∧ q=(d:ℚ)*u^2) →
        scalarClass q hq = 1 ∨ scalarClass q hq = scalarClass (15569 : ℚ) (by norm_num) := by
      intro q hq hh
      obtain ⟨d,hd,u,hu,heq⟩ := hh
      rcases hd with hd | hd
      · left
        apply (scalarClass_eq_one_iff q hq).mpr
        refine ⟨u,?_⟩
        simpa [hd,pow_two] using heq
      · right
        apply scalarClass_eq_of_mul_square (q := u)
        simpa [hd] using heq
    fin_cases i
    · exact helper hx hc.1
    · exact helper hm hc.2.1
    · exact helper hp hc.2.2

#print axioms supported_local_square
#print axioms depth_two_global_classes
#print axioms depth_two_real_identity
#print axioms entire_H_kummer_support
end FourCorner.Cs15569Completion
