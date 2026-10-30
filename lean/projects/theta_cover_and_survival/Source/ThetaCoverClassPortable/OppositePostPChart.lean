import ThetaCoverClassPortable.Slot02HighRatios

noncomputable section
open AlgebraicGeometry MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.OppositeProjective.PostPChart
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- P=1, with affine coordinates ordered T,Q,R,Z. -/
def dehomP : OppositeHomogeneousQuadrics.Ambient K →+* OppositeHomogeneousQuadrics.AffineAmbient K :=
  eval₂Hom C ![1,X 1,X 2,X 3,X 0]
def affineEquation (mu nu : K) : Fin 3 → OppositeHomogeneousQuadrics.AffineAmbient K
  | 0 => X 3^2 - C (OppositePolynomials.A mu nu) + C (2*OppositePolynomials.A mu nu*nu^2)*X 0^2
  | 1 => X 1^2 - 1 - C (mu^2)*X 0^2 - C 2*(X 3*X 0)
  | 2 => X 2^2 - 1 - C (mu^2)*X 0^2 + C 2*(X 3*X 0)
abbrev affineIdeal (mu nu : K) := Ideal.span (Set.range (affineEquation mu nu))
abbrev affineRing (mu nu : K) := OppositeHomogeneousQuadrics.AffineAmbient K ⧸ affineIdeal mu nu
lemma dehomP_quadric (mu nu : K) (i : Fin 3) :
    dehomP (OppositeHomogeneousQuadrics.quadric mu nu i) = affineEquation mu nu i := by
  fin_cases i <;> simp [dehomP,OppositeHomogeneousQuadrics.quadric,
    OppositeHomogeneousQuadrics.F0,OppositeHomogeneousQuadrics.F1,OppositeHomogeneousQuadrics.F2,affineEquation]
lemma dehomP_ideal (mu nu : K) :
    Ideal.map dehomP (OppositeHomogeneousQuadrics.ideal mu nu) = affineIdeal mu nu := by
  rw [OppositeHomogeneousQuadrics.ideal, Ideal.map_span, ← Set.range_comp]
  exact congrArg Ideal.span (congrArg Set.range (funext (dehomP_quadric mu nu)))
def dehomQuotient (mu nu : K) : coordinateRing mu nu →+* affineRing mu nu :=
  Ideal.quotientMap (affineIdeal mu nu) dehomP
    ((Ideal.map_le_iff_le_comap).mp (le_of_eq (dehomP_ideal mu nu)))

abbrev ambientAway := Away (grading K) (X (0 : Fin 5))

/-- Evaluate the ordinary localization by P=1, then restrict to its degree-zero subring. -/
def ambientDehom : ambientAway (K := K) →+* OppositeHomogeneousQuadrics.AffineAmbient K :=
  (IsLocalization.Away.lift (S := Localization.Away (X (0 : Fin 5) : OppositeHomogeneousQuadrics.Ambient K))
    (X 0) (g := dehomP)
    (by simpa [dehomP] using (isUnit_one : IsUnit (1 : OppositeHomogeneousQuadrics.AffineAmbient K)))).comp
    (algebraMap _ _)

lemma ambientDehom_mk (d : ℕ) (p : OppositeHomogeneousQuadrics.Ambient K)
    (hp : p ∈ grading K (d • 1)) :
    ambientDehom (Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 4 0) d p hp) =
      dehomP p := by
  let l : Localization.Away (X (0 : Fin 5) : OppositeHomogeneousQuadrics.Ambient K) →+* OppositeHomogeneousQuadrics.AffineAmbient K := IsLocalization.Away.lift (S := Localization.Away (X (0 : Fin 5) : OppositeHomogeneousQuadrics.Ambient K))
    (X 0) (g := dehomP)
    (by simpa [dehomP] using (isUnit_one : IsUnit (1 : OppositeHomogeneousQuadrics.AffineAmbient K)))
  have h : l (Localization.mk p ⟨X 0 ^ d, ⟨d, rfl⟩⟩) * l (algebraMap (OppositeHomogeneousQuadrics.Ambient K) (Localization.Away (X (0 : Fin 5) : OppositeHomogeneousQuadrics.Ambient K)) ((X (0 : Fin 5)) ^ d)) =
      l (algebraMap _ _ p) := by
    rw [← map_mul, Localization.mk_eq_mk', IsLocalization.mk'_spec]
  simpa [ambientDehom, l, IsLocalization.Away.lift_eq, dehomP] using h

lemma ambientDehom_ratio (j : Fin 5) :
    ambientDehom (Slot02HighProjSpace.ratio K 4 0 j) =
      dehomP (X j) := by
  exact ambientDehom_mk 1 _ _

def ambientInverse : OppositeHomogeneousQuadrics.AffineAmbient K →+* ambientAway (K := K) :=
  MvPolynomial.eval₂Hom (algebraMap K _) (fun j => Slot02HighProjSpace.ratio K 4 0 (![4,1,2,3] j))

lemma ambientDehom_inverse :
    ambientDehom.comp (ambientInverse (K := K)) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, ambientInverse, coe_eval₂Hom, eval₂_C, RingHom.id_apply]
    change ambientDehom (algebraMap K _ a) = C a
    change ambientDehom (Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 4 0) 0 (C a) _) = C a
    rw [ambientDehom_mk]
    simp [dehomP]
  · intro j
    simp only [RingHom.comp_apply, ambientInverse, coe_eval₂Hom, eval₂_X, RingHom.id_apply, ambientDehom_ratio]
    fin_cases j <;> simp [dehomP]

lemma ambientInverse_dehom_ratio (j : Fin 5) :
    ambientInverse (ambientDehom (Slot02HighProjSpace.ratio K 4 0 j)) =
      Slot02HighProjSpace.ratio K 4 0 j := by
  rw [ambientDehom_ratio]
  fin_cases j <;> simp [dehomP, ambientInverse,
    Slot02HighProjSpace.ratio_self]

lemma ambientInverse_dehom :
    (ambientInverse (K := K)).comp ambientDehom = RingHom.id _ := by
  apply RingHom.ext
  intro z
  change ambientInverse (ambientDehom z) = z
  have hz : z ∈ Algebra.adjoin K (Set.range (Slot02HighProjSpace.ratio K 4 0)) := by
    rw [Slot02HighProjSpace.adjoin_range_ratio]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    exact ambientInverse_dehom_ratio (K := K) j
  | algebraMap a =>
    change ambientInverse (ambientDehom (algebraMap K _ a)) = algebraMap K _ a
    have h : ambientDehom (algebraMap K _ a) = C a := by
      change ambientDehom (Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 4 0) 0 (C a) _) = C a
      rw [ambientDehom_mk]; simp [dehomP]
    rw [h]
    simp [ambientInverse]
  | add x y hx hy hxe hye => simpa only [map_add] using congrArg₂ (· + ·) hxe hye
  | mul x y hx hy hxe hye => simpa only [map_mul] using congrArg₂ (· * ·) hxe hye

/-- The genuine ambient standard P-chart has the expected four affine coordinates. -/
def ambientEquiv : ambientAway (K := K) ≃+* OppositeHomogeneousQuadrics.AffineAmbient K :=
  RingEquiv.ofRingHom ambientDehom ambientInverse ambientDehom_inverse ambientInverse_dehom


/-- The genuine degree-zero localization defining the project's P-chart. -/
abbrev chartRing (mu nu : K) := Away (quotientGrading mu nu)
  (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (0 : Fin 5)))

abbrev quotientMap (mu nu : K) := quotientGradedMap (grading K)
  (OppositeHomogeneousQuadrics.homogeneousIdeal mu nu)

def chartQuotient (mu nu : K) : ambientAway (K := K) →+* chartRing mu nu :=
  Away.map (quotientMap mu nu) (X (0 : Fin 5))

lemma chartQuotient_surjective (mu nu : K) : Function.Surjective (chartQuotient mu nu) :=
  FourCorner.ProjectiveLocalization.away_map_surjective (quotientMap mu nu)
    (quotientGradedMap_surjective (grading K) (OppositeHomogeneousQuadrics.homogeneousIdeal mu nu))
    (Slot02HighProjSpace.X_mem_one K 4 0)

lemma dehomQuotient_T (mu nu : K) :
    dehomQuotient mu nu (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (0 : Fin 5))) = 1 := by
  simp [dehomQuotient, Ideal.quotientMap, dehomP]

/-- P evaluates to one, so actual ordinary localization and degree-zero restriction apply. -/
def chartDehom (mu nu : K) : chartRing mu nu →+* affineRing mu nu :=
  (IsLocalization.Away.lift (S := Localization.Away
    (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (0 : Fin 5))))
    _ (g := dehomQuotient mu nu) (by rw [dehomQuotient_T]; exact isUnit_one)).comp
    (algebraMap _ _)

lemma chartDehom_mk (mu nu : K) (d : ℕ) (p : coordinateRing mu nu)
    (hp : p ∈ quotientGrading mu nu (d • 1)) :
    chartDehom mu nu (Away.mk (quotientGrading mu nu)
      ((quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 0)) d p hp) =
      dehomQuotient mu nu p := by
  let t := Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (0 : Fin 5))
  let l : Localization.Away t →+* affineRing mu nu :=
    IsLocalization.Away.lift t (g := dehomQuotient mu nu)
      (by rw [dehomQuotient_T]; exact isUnit_one)
  have h : l (Localization.mk p ⟨t ^ d, ⟨d, rfl⟩⟩) *
      l (algebraMap (coordinateRing mu nu) (Localization.Away t) (t ^ d)) =
      l (algebraMap _ _ p) := by
    rw [← map_mul, Localization.mk_eq_mk', IsLocalization.mk'_spec]
  simpa [chartDehom, l, IsLocalization.Away.lift_eq, t, dehomQuotient_T] using h

lemma dehom_square (mu nu : K) :
    (chartDehom mu nu).comp (chartQuotient mu nu) =
      (Ideal.Quotient.mk (affineIdeal mu nu)).comp ambientDehom := by
  apply RingHom.ext
  intro z
  obtain ⟨d,p,hp,rfl⟩ := Away.mk_surjective (grading K)
    (Slot02HighProjSpace.X_mem_one K 4 0) z
  change chartDehom mu nu (Away.map (quotientMap mu nu) _ _) = _
  rw [Away.map_mk]
  have h := chartDehom_mk mu nu d ((quotientMap mu nu) p) ((quotientMap mu nu).map_mem hp)
  change chartDehom mu nu _ = _ at h
  erw [h]
  change dehomQuotient mu nu ((quotientMap mu nu) p) =
    Ideal.Quotient.mk (affineIdeal mu nu) (ambientDehom _)
  rw [ambientDehom_mk]
  rfl

lemma inverse_affineEquation (mu nu : K) (i : Fin 3) :
    ambientInverse (affineEquation mu nu i) =
      Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 4 0) 2
        (OppositeHomogeneousQuadrics.quadric mu nu i)
        (by simpa using ((mem_homogeneousSubmodule 2 _).mpr
          (OppositeHomogeneousQuadrics.quadric_homogeneous mu nu i))) := by
  apply (ambientEquiv (K := K)).injective
  change ambientDehom (ambientInverse _) = ambientDehom _
  have h := RingHom.congr_fun (ambientDehom_inverse (K := K))
    (affineEquation mu nu i)
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h, ambientDehom_mk]
  exact (dehomP_quadric mu nu i).symm

lemma chartQuotient_inverse_equation (mu nu : K) (i : Fin 3) :
    chartQuotient mu nu (ambientInverse (affineEquation mu nu i)) = 0 := by
  rw [inverse_affineEquation]
  change Away.map (quotientMap mu nu) _ _ = 0
  rw [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, val_zero]
  have h : (quotientMap mu nu) (OppositeHomogeneousQuadrics.quadric mu nu i) = 0 :=
    equation_vanishes mu nu i
  rw [h, Localization.mk_zero]

/-- The inverse uses the genuine projective ratios and descends through exactly the affine equations. -/
def chartInverse (mu nu : K) : affineRing mu nu →+* chartRing mu nu :=
  Ideal.Quotient.lift (affineIdeal mu nu) ((chartQuotient mu nu).comp ambientInverse) (by
    have h : affineIdeal mu nu ≤ RingHom.ker ((chartQuotient mu nu).comp ambientInverse) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact RingHom.mem_ker.mpr (chartQuotient_inverse_equation mu nu i)
    exact fun a ha => h ha)

lemma chartInverse_mk (mu nu : K) (p : OppositeHomogeneousQuadrics.AffineAmbient K) :
    chartInverse mu nu (Ideal.Quotient.mk (affineIdeal mu nu) p) =
      chartQuotient mu nu (ambientInverse p) := rfl

lemma chartDehom_inverse (mu nu : K) :
    (chartDehom mu nu).comp (chartInverse mu nu) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change chartDehom mu nu (chartInverse mu nu (Ideal.Quotient.mk (affineIdeal mu nu) p)) = _
  rw [chartInverse_mk]
  have h := RingHom.congr_fun (dehom_square mu nu) (ambientInverse p)
  simp only [RingHom.comp_apply] at h
  rw [h]
  change Ideal.Quotient.mk (affineIdeal mu nu) (ambientDehom (ambientInverse p)) = _
  have h := RingHom.congr_fun (ambientDehom_inverse (K := K)) p
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h]
  rfl

lemma chartInverse_dehom (mu nu : K) :
    (chartInverse mu nu).comp (chartDehom mu nu) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := chartQuotient_surjective mu nu x
  change chartInverse mu nu (chartDehom mu nu (chartQuotient mu nu p)) = chartQuotient mu nu p
  have h := RingHom.congr_fun (dehom_square mu nu) p
  simp only [RingHom.comp_apply] at h
  rw [h]
  change chartInverse mu nu (Ideal.Quotient.mk (affineIdeal mu nu) (ambientDehom p)) = _
  rw [chartInverse_mk]
  have h := RingHom.congr_fun (ambientInverse_dehom (K := K)) p
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h]

/-- The actual P-chart of the three-quadric Proj equals the literal four-variable affine quotient. -/
def chartEquiv (mu nu : K) : chartRing mu nu ≃+* affineRing mu nu :=
  RingEquiv.ofRingHom (chartDehom mu nu) (chartInverse mu nu)
    (chartDehom_inverse mu nu) (chartInverse_dehom mu nu)

end FourCorner.OppositeProjective.PostPChart
#print axioms FourCorner.OppositeProjective.PostPChart.ambientEquiv
#print axioms FourCorner.OppositeProjective.PostPChart.chartEquiv
