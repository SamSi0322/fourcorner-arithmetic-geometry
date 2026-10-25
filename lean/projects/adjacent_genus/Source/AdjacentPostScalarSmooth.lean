import AdjacentPostTwoChartCover

noncomputable section
namespace FourCorner.AdjacentPostScalar
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1000000

/-- A zero of the literal plus-distance function is transverse to the conic.
The only excluded crossing parameter is the explicitly proved exceptional factor. -/
theorem plus_det_ne_zero (q u v : K) (hq : q ≠ 0) (hA : q-1 ≠ 0)
    (ht : q^2-6*q+1 ≠ 0)
    (h0 : (q-1)*u^2+q*v^2-q*(q-1)=0)
    (hp : (u+1)^2+(v-2)^2=0) : u*v+2*(q-1)*u+q*v ≠ 0 := by
  intro hD
  by_cases hv2 : v=2
  · have hu1 : u+1=0 := (sq_eq_zero_iff (a := u+1)).mp (by simpa [hv2] using hp)
    have hu : u = -1 := by linear_combination hu1
    apply ht
    rw [hu,hv2] at h0
    linear_combination -h0
  · have hvn : v-2 ≠ 0 := sub_ne_zero.mpr hv2
    let j := -(u+1)/(v-2)
    have hline0 : u+1+j*(v-2)=0 := by
      dsimp [j]
      field_simp
      ring
    have hline : u+j*v+1-2*j=0 := by linear_combination hline0
    have hj : j^2+1=0 := by
      dsimp [j]
      field_simp
      linear_combination hp
    have htanprod : (v-2)*((q-1)*u+q*j*v)=0 := by
      linear_combination -hD+q*v*hline0
    have htan : (q-1)*u+q*j*v=0 :=
      ((mul_eq_zero (a := v-2) (b := (q-1)*u+q*j*v)).mp htanprod).resolve_left hvn
    have hu : u=q*(2*j-1) := by linear_combination q*hline-htan
    have hvprod : q*(v+(q-1)*(j+2))=0 := by
      linear_combination -j*htan+(q-1)*j*hu+q*v*hj+2*(q-1)*q*hj
    have hv : v= -(q-1)*(j+2) := by
      have h := ((mul_eq_zero (a := q) (b := v+(q-1)*(j+2))).mp hvprod).resolve_left hq
      linear_combination h
    rw [hu,hv] at h0
    have hprod : q*(q-1)*(1+j)=0 := by
      linear_combination -(1/4 : K)*h0+(q*(q-1)*(5*q-1)/4)*hj
    have hjm : 1+j=0 :=
      ((mul_eq_zero (a := q*(q-1)) (b := 1+j)).mp hprod).resolve_left (mul_ne_zero hq hA)
    have htwo : (2 : K)=0 := by linear_combination hj-(j-1)*hjm
    norm_num at htwo

/-- The two zero sets are disjoint under the exact exceptional-factor hypothesis. -/
theorem not_both_roots_zero (q u v p r : K) (hi : q^2-8*q+32 ≠ 0)
    (h0 : (q-1)*u^2+q*v^2-q*(q-1)=0)
    (hp : p^2=(u+1)^2+(v-2)^2) (hr : r^2=(u-1)^2+(v-2)^2)
    (hq : q ≠ 0) : ¬(p=0 ∧ r=0) := by
  rintro ⟨hP,hR⟩
  rw [hP] at hp
  rw [hR] at hr
  have hu : u=0 := by linear_combination -(1/4 : K)*hp+(1/4 : K)*hr
  rw [hu] at h0 hp hr
  have hV2 : v^2=q-1 := by
    have hprod : q*(v^2-(q-1))=0 := by linear_combination h0
    exact sub_eq_zero.mp (((mul_eq_zero (a := q) (b := v^2-(q-1))).mp hprod).resolve_left hq)
  have hV : 4*v=q+4 := by linear_combination hV2+hp
  apply hi
  linear_combination 16*hV2-(4*v+q+4)*hV

/-- Four actual Jacobian minors cover every field-valued point of the literal affine source. -/
theorem nonzero_minor_alternative (c u v p r : K) (h : AdjacentPolynomials.Admissible c)
    (h0 : (c^2-1)*u^2+c^2*v^2-c^2*(c^2-1)=0)
    (hp : p^2=(u+1)^2+(v-2)^2) (hr : r^2=(u-1)^2+(v-2)^2) :
    8*(c^2-1)*u*p*r ≠ 0 ∨ 8*c^2*v*p*r ≠ 0 ∨
      8*r*(u*v+2*(c^2-1)*u+c^2*v) ≠ 0 ∨
      8*p*(u*v+2*(c^2-1)*u-c^2*v) ≠ 0 := by
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 h.c_ne_zero
  have ht : (c^2)^2-6*c^2+1 ≠ 0 := by
    intro hz
    apply h.tangency_ne_zero
    linear_combination hz
  have hi : (c^2)^2-8*c^2+32 ≠ 0 := by
    intro hz
    apply h.intersection_ne_zero
    linear_combination hz
  by_cases hP : p=0
  · have hR : r ≠ 0 := fun hR => not_both_roots_zero (c^2) u v p r hi h0 hp hr hc2 ⟨hP,hR⟩
    have hplus : (u+1)^2+(v-2)^2=0 := by rw [← hp,hP]; simp
    have hdet := plus_det_ne_zero (c^2) u v hc2 h.conic_ne_zero ht h0 hplus
    exact Or.inr (Or.inr (Or.inl (mul_ne_zero (mul_ne_zero (by norm_num) hR) hdet)))
  by_cases hR : r=0
  · have hminus : ((-u)+1)^2+(v-2)^2=0 := by
      have hh : (u-1)^2+(v-2)^2=0 := by rw [← hr,hR]; simp
      linear_combination hh
    have he : (c^2-1)*(-u)^2+c^2*v^2-c^2*(c^2-1)=0 := by linear_combination h0
    have hdet := plus_det_ne_zero (c^2) (-u) v hc2 h.conic_ne_zero ht he hminus
    have hd : u*v+2*(c^2-1)*u-c^2*v ≠ 0 := by
      intro hz
      apply hdet
      linear_combination -hz
    exact Or.inr (Or.inr (Or.inr (mul_ne_zero (mul_ne_zero (by norm_num) hP) hd)))
  by_cases hU : u=0
  · have hV : v ≠ 0 := by
      intro hv
      apply mul_ne_zero hc2 h.conic_ne_zero
      rw [hU,hv] at h0
      linear_combination -h0
    exact Or.inr (Or.inl (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) hc2) hV) hP) hR))
  exact Or.inl (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) h.conic_ne_zero) hU) hP) hR)

#print axioms plus_det_ne_zero
#print axioms not_both_roots_zero
#print axioms nonzero_minor_alternative
end FourCorner.AdjacentPostScalar
