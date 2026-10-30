import ThetaCoverClassPortable.ThetaLinesSchemePoints
import ThetaCoverClassPortable.FourCorner.ThetaBitangentExhaustionWave36

namespace FourCorner.ThetaLinesContactPoints
open AlgebraicGeometry CategoryTheory ThetaLinesSchemePoints ThetaLiteralModels
noncomputable section
variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
attribute [local instance] Classical.propDecidable

/-- Every actual affine-line square restriction has nonzero leading quartic
coefficient, proved from the exhaustive classification including hyperflexes. -/
theorem affine_leading_ne_zero (α β : k) (h : IsThetaSquareContact (.affine α β)) : thetaA4 α β ≠ 0 := by
  have hf : thetaA4 α β=9801-39592*α^2+39984*(α^2)^2 := by unfold thetaA4;ring
  rw [hf]
  have hc := theta_square_contact_classification (.affine α β) h
  rcases hc with ⟨_,hα|hα⟩ | ⟨hα,_⟩ | ⟨hα,_⟩ | ⟨hα,_⟩ | ⟨hα,_⟩ | ⟨hα,_⟩
  all_goals rw [hα] <;> norm_num

theorem quadratic_affine_roots (a b c : k) (ha : a ≠ 0) (hd : b^2-4*a*c ≠ 0) :
    ∃x y : k,x ≠ y ∧ a*x^2+b*x+c=0 ∧ a*y^2+b*y+c=0 := by
  obtain ⟨d,hd2⟩ := IsAlgClosed.exists_pow_nat_eq (b^2-4*a*c) (by decide : 0<2)
  have hd0 : d ≠ 0 := by intro h;apply hd;simpa [h] using hd2.symm
  have hden : 2*a ≠ 0 := mul_ne_zero (by norm_num) ha
  have root (e : k) (he : e^2=b^2-4*a*c) : a*((-b+e)/(2*a))^2+b*((-b+e)/(2*a))+c=0 := by
    field_simp
    linear_combination he
  refine ⟨(-b+d)/(2*a),(-b-d)/(2*a),?_,root d hd2,?_⟩
  · intro h
    have hh := congrArg (fun z : k => z*(2*a)) h
    simp only [div_mul_cancel₀ _ hden] at hh
    have hz : d=0 := by linear_combination (1/2:k)*hh
    exact hd0 hz
  · simpa only [sub_eq_add_neg] using root (-d) (by simpa using hd2)

/-- The two contact roots give two DISTINCT ACTUAL rational scheme points
of the original quartic D, in its Y=1 chart. -/
theorem affine_two_actual_points (α β : k) (h : IsThetaSquareContact (.affine α β)) :
    ∃x y : k,∃hx : thetaF x 1 (α*x+β)=0,∃hy : thetaF y 1 (α*y+β)=0,
      x ≠ y ∧ affinePoint α β x hx ≠ affinePoint α β y hy ∧
      affinePoint α β x hx ≫ dToBase k=𝟙 _ ∧ affinePoint α β y hy ≫ dToBase k=𝟙 _ := by
  have hn := affine_leading_ne_zero α β h
  obtain ⟨c,a,b,d,hc,hd,he⟩ := (theta_no_hyperflex (.affine α β)).mp h
  have ha : a ≠ 0 := by
    intro hz
    have hh := he 1 0
    simp only [ThetaLine.restrict,thetaF] at hh
    have hh' : thetaA4 α β=c*a^2 := by simpa [ThetaLine.restrict,thetaF,thetaA4] using he 1 0
    exact hn (by simp [hz] at hh';simpa using hh')
  obtain ⟨x,y,hxy,hx,hy⟩ := quadratic_affine_roots a b d ha hd
  have hx' : thetaF x 1 (α*x+β)=0 := by simpa [ThetaLine.restrict,hx] using he x 1
  have hy' : thetaF y 1 (α*y+β)=0 := by simpa [ThetaLine.restrict,hy] using he y 1
  refine ⟨x,y,hx',hy',hxy,?_,point_over _ _ _,point_over _ _ _⟩
  intro hp
  exact hxy (affinePoint_injective _ _ _ _ _ _ hp)

/-- The two vertical-line contact roots give two distinct ACTUAL original
D points, now in its Z=1 chart. -/
theorem vertical_two_actual_points (t : k) (h : IsThetaSquareContact (.vertical t)) :
    ∃x y : k,∃hx : thetaF (t*x) x 1=0,∃hy : thetaF (t*y) y 1=0,
      x ≠ y ∧ verticalPoint t x hx ≠ verticalPoint t y hy ∧
      verticalPoint t x hx ≫ dToBase k=𝟙 _ ∧ verticalPoint t y hy ≫ dToBase k=𝟙 _ := by
  have hb := (theta_no_hyperflex (.vertical t)).mp h
  have hn := (theta_even_square_discriminant (by norm_num : (39984:k) ≠ 0)
    ((theta_vertical_bitangent_iff t).mp hb)).1
  obtain ⟨c,a,b,d,hc,hd,he⟩ := hb
  have hh : 9801*(t^4+1)+19598*t^2=c*a^2 := by simpa [ThetaLine.restrict,thetaF] using he 1 0
  have ha : a ≠ 0 := by intro hz;apply hn;simpa [hz] using hh
  obtain ⟨x,y,hxy,hx,hy⟩ := quadratic_affine_roots a b d ha hd
  have hx' : thetaF (t*x) x 1=0 := by simpa [ThetaLine.restrict,hx] using he x 1
  have hy' : thetaF (t*y) y 1=0 := by simpa [ThetaLine.restrict,hy] using he y 1
  refine ⟨x,y,hx',hy',hxy,?_,point_over _ _ _,point_over _ _ _⟩
  intro hp
  exact hxy (verticalPoint_injective _ _ _ _ _ hp)

#print axioms affine_leading_ne_zero
#print axioms quadratic_affine_roots
#print axioms affine_two_actual_points
#print axioms vertical_two_actual_points
end
end FourCorner.ThetaLinesContactPoints
