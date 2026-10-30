import ThetaContactDifferentialDivisors

namespace FourCorner.ThetaActualHalfCanonicalContacts
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaGeometricContactPoints ThetaActualLineDifferentials
open ThetaContactDifferentialDivisors ThetaDNaturalGlobalDifferentials
open SmoothProperRationalPointPlaces
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : Module K Γ(toBase.kaehler,⊤) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤

def placeOfPoint (P : RationalPoint toBase) : Place K field := (pointEquivRationalPlace toBase P).val

def pointDivisor (P : RationalPoint toBase) : Divisor K field := Finsupp.single (placeOfPoint P) 1

/-- A true actual-geometric contact datum, for a TRUE global Kähler section:
two distinct ACTUAL original-curve K-points, their actual native places, and
an exact doubled divisor of its TRUE generic germ. No oddness/Pic comparison
is inserted in this geometry-only datum. -/
structure ContactData (s : Γ(toBase.kaehler,⊤)) where
  P : RationalPoint toBase
  Q : RationalPoint toBase
  points_distinct : P≠Q
  places_distinct : placeOfPoint P≠placeOfPoint Q
  germ_ne_zero : genericGerm s≠0
  doubled_divisor : canonicalDivisorOf germ_ne_zero=2 • (pointDivisor P+pointDivisor Q)

 theorem double_points (P Q : Place K field) :
    (2:ℕ) • (Finsupp.single P (1:ℤ)+Finsupp.single Q 1)=Finsupp.single P 2+Finsupp.single Q 2 := by
  rw [two_smul]
  ext w
  simp only [Finsupp.add_apply,Finsupp.single_apply]
  split_ifs <;> norm_num

 def ContactData.divisor {s : Γ(toBase.kaehler,⊤)} (data : ContactData s) : Divisor K field :=
  pointDivisor data.P+pointDivisor data.Q

 theorem ContactData.effective {s : Γ(toBase.kaehler,⊤)} (data : ContactData s) : 0≤data.divisor := by
  intro w
  simp only [ContactData.divisor,pointDivisor,Finsupp.add_apply,Finsupp.single_apply]
  split_ifs <;> norm_num

 theorem ContactData.degree_two {s : Γ(toBase.kaehler,⊤)} (data : ContactData s) : Divisor.degree data.divisor=2 := by
  simp [ContactData.divisor,pointDivisor,map_add,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed]

 theorem ContactData.half_canonical {s : Γ(toBase.kaehler,⊤)} (data : ContactData s) :
    2 • data.divisor=canonicalDivisorOf data.germ_ne_zero := data.doubled_divisor.symm

 theorem affine_contact_data (α β : K) (h : IsThetaSquareContact (.affine α β)) :
    Nonempty (ContactData (affineGlobalSection α β)) := by
  obtain ⟨x,y,hx,hy,hxy,hpq,hd⟩ := affine_contact_divisor α β h
  refine ⟨⟨affinePoint α β x hx,affinePoint α β y hy,?_,hpq,affineDifferential_ne_zero α β,?_⟩⟩
  · intro he
    exact hxy (affinePoint_injective α β x y hx hy he)
  · rw [hd]
    exact (double_points (affinePlace α β x hx) (affinePlace α β y hy)).symm

 theorem vertical_contact_data (t : K) (h : IsThetaSquareContact (.vertical t)) :
    Nonempty (ContactData (verticalGlobalSection t)) := by
  obtain ⟨x,y,hx,hy,hxy,hpq,hd⟩ := vertical_contact_divisor t h
  refine ⟨⟨verticalPoint t x hx,verticalPoint t y hy,?_,hpq,verticalDifferential_ne_zero t,?_⟩⟩
  · intro he
    exact hxy (verticalPoint_injective t x y hx hy he)
  · rw [hd]
    exact (double_points (verticalPlace t x hx) (verticalPlace t y hy)).symm

#print axioms ContactData.effective
#print axioms ContactData.degree_two
#print axioms ContactData.half_canonical
#print axioms affine_contact_data
#print axioms vertical_contact_data
end
end FourCorner.ThetaActualHalfCanonicalContacts
