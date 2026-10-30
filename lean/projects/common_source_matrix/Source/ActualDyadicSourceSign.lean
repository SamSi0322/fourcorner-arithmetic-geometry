import ActualCharacterSign

noncomputable section
namespace FourCorner.CommonSource

/-- The exact whole-H formal-parameter character satisfies the source sign
relation. All finite-point, nonzero-slot, torsion-order, and depth bridges are
proved from the same rational source. -/
theorem actual_source_dyadic_sign {n : ℤ} (hn : n ≠ 0)
    (hn8 : n%8=1 ∨ n%8=7) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k)
    {a b c e u v : ℚ}
    (hQ : CongruentEquation (n:ℚ) a b) (hR : CongruentEquation (n:ℚ) c e)
    (ha : a ≠ 0) (hc : c ≠ 0) (ham : a-n ≠ 0) (hcm : c-n ≠ 0)
    (hap : a+n ≠ 0) (hcp : c+n ≠ 0)
    (hu : u^2= -(a*c)/n) (hv : v^2= -((a-n)*(c-n))/n)
    (U V : H n hn) (τQ τR : Point (n:ℚ))
    (htQ : 2 • τQ=0) (htR : 2 • τR=0)
    (hQU : finitePoint (by exact_mod_cast hn) hQ=(U:Point (n:ℚ))+τQ)
    (hRV : finitePoint (by exact_mod_cast hn) hR=(V:Point (n:ℚ))+τR)
    (hf : Even (commonSourceReturn (n:ℚ_[2]) a c).valuation) :
    paperDyadicCharacter15 n hn k hk hdeep U=paperDyadicCharacter15 n hn k hk hdeep V ∨
    paperDyadicCharacter15 n hn k hk hdeep U= -paperDyadicCharacter15 n hn k hk hdeep V := by
  obtain ⟨x,y,hE,hUP,hxd⟩ := source_remainder_coordinates hn hQ ha ham hap
    U τQ U.property htQ hQU
  obtain ⟨w,z,hF,hVP,hwd⟩ := source_remainder_coordinates hn hR hc hcm hcp
    V τR V.property htR hRV
  have hUH : finitePoint (by exact_mod_cast hn) hE ∈ H n hn := by rw [← hUP];exact U.property
  have hVH : finitePoint (by exact_mod_cast hn) hF ∈ H n hn := by rw [← hVP];exact V.property
  have hQU' : finitePoint (by exact_mod_cast hn) hQ=finitePoint (by exact_mod_cast hn) hE+τQ := by
    simpa only [hUP] using hQU
  have hRV' : finitePoint (by exact_mod_cast hn) hR=finitePoint (by exact_mod_cast hn) hF+τR := by
    simpa only [hVP] using hRV
  have hd := actual_source_even_return_same_depth hn hn8 hQ hR hE hF
    ha hc ham hcm hap hcp hu hv hUH hVH τQ τR htQ htR hQU' hRV' hf
  let P := paperHToLevel15 n hn k hdeep U
  let Q := paperHToLevel15 n hn k hdeep V
  have hP : (P : Point (n:ℚ)) = .some x y (nonsingular (by exact_mod_cast hn) hE) := hUP
  have hV : (Q : Point (n:ℚ)) = .some w z (nonsingular (by exact_mod_cast hn) hF) := hVP
  exact actual_character_sign_of_equal_depth n hn k hk P Q x y w z
    (nonsingular (by exact_mod_cast hn) hE) (nonsingular (by exact_mod_cast hn) hF) hP hV hd

#print axioms actual_source_dyadic_sign
end FourCorner.CommonSource
