import ThetaLiteralModels
import ThetaProjMap
noncomputable section
namespace FourCorner.ThetaProjection
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ThetaLiteralModels ThetaProjectiveModel
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k : Type u} [Field k] [CharZero k]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
abbrev sG := grading (sourceEquation k) (source_homogeneous k)
abbrev dG := grading (targetEquation k) (target_homogeneous k)
abbrev sR := MvPolynomial (Fin 5) k ⧸ (ideal (sourceEquation k) (source_homogeneous k)).toIdeal
abbrev dR := MvPolynomial (Fin 3) k ⧸ (ideal (targetEquation k) (target_homogeneous k)).toIdeal
abbrev sqmap := ThetaQuotientChart.quotientMap (sourceEquation k) (source_homogeneous k)
abbrev dqmap := ThetaQuotientChart.quotientMap (targetEquation k) (target_homogeneous k)
def sx (j : Fin 5) : sR (k:=k) := sqmap (X j)
lemma source_relations : sx (k:=k) 0^2=sx 3^2+50*sx 4^2 ∧
    sx (k:=k) 1^2=sx 3^2+14*sx 3*sx 4+51*sx 4^2 ∧
    sx (k:=k) 2^2=sx 3^2-14*sx 3*sx 4+51*sx 4^2 := by
  have h (i : Fin 3) : sqmap (sourceEquation k i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  have h0:=h 0;have h1:=h 1;have h2:=h 2
  simp [sourceEquation,map_ofNat] at h0 h1 h2
  change _ ∧ _ ∧ _
  dsimp [sx,sqmap,ThetaQuotientChart.quotientMap,quotientGradedMap]
  exact ⟨by linear_combination h0,by linear_combination h1,by linear_combination h2⟩
lemma quartic_identity {A : Type*} [CommRing A] {p q r z t : A}
    (hp : p^2=z^2+50*t^2) (hq : q^2=z^2+14*z*t+51*t^2)
    (hr : r^2=z^2-14*z*t+51*t^2) :
    9801*(q^4+r^4)+19598*q^2*r^2-39592*(q^2+r^2)*p^2+39984*p^4=0 := by
  linear_combination
    (39984*p^2 + 39984*z^2 + 1999200*t^2 - 39592*(q^2+r^2))*hp +
    (9801*q^2 + 9801*(z^2+14*z*t+51*t^2) + 19598*r^2 -
      39592*(z^2+50*t^2))*hq +
    (9801*r^2 + 9801*(z^2-14*z*t+51*t^2) +
      19598*(z^2+14*z*t+51*t^2) -39592*(z^2+50*t^2))*hr

def ambientProjection : homogeneousSubmodule (Fin 3) k →+*ᵍ homogeneousSubmodule (Fin 5) k where
  __ := eval₂Hom C ![X 1,X 2,X 0]
  map_mem {i} {p} hp := by
    have hg (j : Fin 3) : (![X 1,X 2,X 0] j : MvPolynomial (Fin 5) k).IsHomogeneous 1 := by
      fin_cases j <;> exact isHomogeneous_X _ _
    have h := hp.eval₂ C ![X 1,X 2,X 0] (fun c=>isHomogeneous_C _ c) hg
    change (eval₂ C ![X 1,X 2,X 0] p).IsHomogeneous i
    simpa only [one_mul] using h
abbrev rawProjection := (sqmap (k:=k)).comp ambientProjection
lemma target_vanishes : rawProjection (k:=k) (targetPolynomial k)=0 := by
  obtain ⟨hp,hq,hr⟩ := source_relations (k:=k)
  have h:=quartic_identity hp hq hr
  change sqmap (ambientProjection (targetPolynomial k))=0
  simp only [targetPolynomial,map_add,map_sub,map_mul,map_pow,ambientProjection,
    GradedRingHom.coe_mk,coe_eval₂Hom,eval₂_C,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_fin_one,map_ofNat]
  dsimp [sx] at h
  have hv : Matrix.vecHead (Matrix.vecTail (![X 2,X 0] : Fin 2 → MvPolynomial (Fin 5) k))=X 0 := rfl
  rw [hv]
  dsimp [sqmap,ThetaQuotientChart.quotientMap,quotientGradedMap]
  linear_combination h

def coordinateMap : dG (k:=k) →+*ᵍ sG (k:=k) where
  __ := Ideal.Quotient.lift _ (rawProjection (k:=k)).toRingHom (by
    have hh : (ideal (targetEquation k) (target_homogeneous k)).toIdeal ≤
        RingHom.ker (rawProjection (k:=k)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact target_vanishes
    exact fun x hx=>hh hx)
  map_mem {i} {a} ha := by
    obtain ⟨p,hp,rfl⟩ := (mem_quotGrading_iff _ _).mp ha
    exact (rawProjection (k:=k)).map_mem hp
lemma coordinateMap_X (j : Fin 3) : coordinateMap (dqmap (k:=k) (X j))=![sx 1,sx 2,sx 0] j := by
  fin_cases j <;> simp [coordinateMap,rawProjection,ambientProjection,sx]

/-- The projection has no base point on the actual Proj prime spectrum. -/
lemma no_base_point (p : ProjectiveSpectrum (sG (k:=k))) :
    ¬ HomogeneousIdeal.irrelevant (dG (k:=k)) ≤ p.1.comap coordinateMap := by
  intro h
  let I := p.asHomogeneousIdeal.toIdeal
  letI : I.IsPrime := p.isPrime
  let B := sR (k:=k) ⧸ I
  letI : IsDomain B := Ideal.Quotient.isDomain I
  let F := FractionRing B
  letI : Algebra k (sR (k:=k)) := Ideal.Quotient.algebra k
  letI : Algebra k B := Ideal.Quotient.algebra k
  letI : CharZero B := charZero_of_injective_algebraMap (algebraMap k B).injective
  letI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective B F)
  let f : sR (k:=k) →+* F := (algebraMap B F).comp (Ideal.Quotient.mk I)
  let x : Fin 5 → F := fun j=> f (sx j)
  have hs : ThetaProjectiveCoordinates.Source (x 0) (x 1) (x 2) (x 3) (x 4) := by
    obtain ⟨h0,h1,h2⟩ := source_relations (k:=k)
    exact ⟨by simpa [x,map_ofNat] using congrArg f h0,
      by simpa [x,map_ofNat] using congrArg f h1,
      by simpa [x,map_ofNat] using congrArg f h2⟩
  have hcoord (j : Fin 3) : coordinateMap (dqmap (k:=k) (X j))∈I := by
    exact h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
      ((dqmap (k:=k)).map_mem (isHomogeneous_X _ _)))
  have hx (j : Fin 3) : f (![sx 1,sx 2,sx 0] j)=0 := by
    rw [←coordinateMap_X]
    have hz:=Ideal.Quotient.eq_zero_iff_mem.mpr (hcoord j)
    change algebraMap B F (Ideal.Quotient.mk I _)=0
    rw [hz,map_zero]
  have hx0 : x 0=0 := by simpa [x] using hx 2
  have hx1 : x 1=0 := by simpa [x] using hx 0
  have hx2 : x 2=0 := by simpa [x] using hx 1
  obtain ⟨hx3,hx4⟩ := ThetaProjectiveCoordinates.no_basepoint hs hx0 hx1 hx2
  have hall (j : Fin 5) : sx (k:=k) j∈I := by
    have hz : x j=0 := by fin_cases j <;> assumption
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (IsFractionRing.injective B F)
    simpa [x,f] using hz
  apply p.not_irrelevant_le
  apply (irrelevant_span (sourceEquation k) (source_homogeneous k)).trans
  exact Ideal.span_le.mpr (by rintro _ ⟨j,rfl⟩;exact hall j)

/-- The literal homogeneous projection [P:Q:R:z:T] ↦ [Q:R:P], as an actual scheme morphism. -/
def projection : C k ⟶ D k := ThetaProjMap.Proj.map coordinateMap no_base_point
lemma projection_preimage (a : dR (k:=k)) : projection (k:=k) ⁻¹ᵁ
    Proj.basicOpen (dG (k:=k)) a = Proj.basicOpen (sG (k:=k)) (coordinateMap a) := rfl
end FourCorner.ThetaProjection
#print axioms FourCorner.ThetaProjection.no_base_point
#print axioms FourCorner.ThetaProjection.projection
