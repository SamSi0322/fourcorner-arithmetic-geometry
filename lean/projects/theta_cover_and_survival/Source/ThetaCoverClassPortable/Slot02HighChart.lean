import ThetaCoverClassPortable.Slot02HighRatios

noncomputable section
open AlgebraicGeometry MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.OppositeProjective.HighChart
universe u
variable {K : Type u} [Field K] [CharZero K]
abbrev ambientAway := Away (grading K) (X (4 : Fin 5))

/-- Evaluate the ordinary localization by T=1, then restrict to its degree-zero subring. -/
def ambientDehom : ambientAway (K := K) →+* OppositeHomogeneousQuadrics.AffineAmbient K :=
  (IsLocalization.Away.lift (S := Localization.Away (X (4 : Fin 5) : OppositeHomogeneousQuadrics.Ambient K))
    (X 4) (g := OppositeHomogeneousQuadrics.dehomT)
    (by simpa [OppositeHomogeneousQuadrics.dehomT] using (isUnit_one : IsUnit (1 : OppositeHomogeneousQuadrics.AffineAmbient K)))).comp
    (algebraMap _ _)

lemma ambientDehom_mk (d : ℕ) (p : OppositeHomogeneousQuadrics.Ambient K)
    (hp : p ∈ grading K (d • 1)) :
    ambientDehom (Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 4 4) d p hp) =
      OppositeHomogeneousQuadrics.dehomT p := by
  let l : Localization.Away (X (4 : Fin 5) : OppositeHomogeneousQuadrics.Ambient K) →+* OppositeHomogeneousQuadrics.AffineAmbient K := IsLocalization.Away.lift (S := Localization.Away (X (4 : Fin 5) : OppositeHomogeneousQuadrics.Ambient K))
    (X 4) (g := OppositeHomogeneousQuadrics.dehomT)
    (by simpa [OppositeHomogeneousQuadrics.dehomT] using (isUnit_one : IsUnit (1 : OppositeHomogeneousQuadrics.AffineAmbient K)))
  have h : l (Localization.mk p ⟨X 4 ^ d, ⟨d, rfl⟩⟩) * l (algebraMap (OppositeHomogeneousQuadrics.Ambient K) (Localization.Away (X (4 : Fin 5) : OppositeHomogeneousQuadrics.Ambient K)) ((X (4 : Fin 5)) ^ d)) =
      l (algebraMap _ _ p) := by
    rw [← map_mul, Localization.mk_eq_mk', IsLocalization.mk'_spec]
  simpa [ambientDehom, l, IsLocalization.Away.lift_eq, OppositeHomogeneousQuadrics.dehomT] using h

lemma ambientDehom_ratio (j : Fin 5) :
    ambientDehom (Slot02HighProjSpace.ratio K 4 4 j) =
      OppositeHomogeneousQuadrics.dehomT (X j) := by
  exact ambientDehom_mk 1 _ _

def ambientInverse : OppositeHomogeneousQuadrics.AffineAmbient K →+* ambientAway (K := K) :=
  MvPolynomial.eval₂Hom (algebraMap K _) (fun j => Slot02HighProjSpace.ratio K 4 4 j.castSucc)

lemma ambientDehom_inverse :
    ambientDehom.comp (ambientInverse (K := K)) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, ambientInverse, coe_eval₂Hom, eval₂_C, RingHom.id_apply]
    change ambientDehom (algebraMap K _ a) = C a
    change ambientDehom (Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 4 4) 0 (C a) _) = C a
    rw [ambientDehom_mk]
    simp [OppositeHomogeneousQuadrics.dehomT]
  · intro j
    simp only [RingHom.comp_apply, ambientInverse, coe_eval₂Hom, eval₂_X, RingHom.id_apply, ambientDehom_ratio]
    fin_cases j <;> simp [OppositeHomogeneousQuadrics.dehomT]

lemma ambientInverse_dehom_ratio (j : Fin 5) :
    ambientInverse (ambientDehom (Slot02HighProjSpace.ratio K 4 4 j)) =
      Slot02HighProjSpace.ratio K 4 4 j := by
  rw [ambientDehom_ratio]
  fin_cases j <;> simp [OppositeHomogeneousQuadrics.dehomT, ambientInverse,
    Slot02HighProjSpace.ratio_self]

lemma ambientInverse_dehom :
    (ambientInverse (K := K)).comp ambientDehom = RingHom.id _ := by
  apply RingHom.ext
  intro z
  change ambientInverse (ambientDehom z) = z
  have hz : z ∈ Algebra.adjoin K (Set.range (Slot02HighProjSpace.ratio K 4 4)) := by
    rw [Slot02HighProjSpace.adjoin_range_ratio]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    exact ambientInverse_dehom_ratio (K := K) j
  | algebraMap a =>
    change ambientInverse (ambientDehom (algebraMap K _ a)) = algebraMap K _ a
    have h : ambientDehom (algebraMap K _ a) = C a := by
      change ambientDehom (Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 4 4) 0 (C a) _) = C a
      rw [ambientDehom_mk]; simp [OppositeHomogeneousQuadrics.dehomT]
    rw [h]
    simp [ambientInverse]
  | add x y hx hy hxe hye => simpa only [map_add] using congrArg₂ (· + ·) hxe hye
  | mul x y hx hy hxe hye => simpa only [map_mul] using congrArg₂ (· * ·) hxe hye

/-- The genuine ambient standard chart has the expected four affine coordinates. -/
def ambientEquiv : ambientAway (K := K) ≃+* OppositeHomogeneousQuadrics.AffineAmbient K :=
  RingEquiv.ofRingHom ambientDehom ambientInverse ambientDehom_inverse ambientInverse_dehom


/-- The genuine degree-zero localization defining the project's T-chart. -/
abbrev chartRing (mu nu : K) := Away (quotientGrading mu nu)
  (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (4 : Fin 5)))

abbrev quotientMap (mu nu : K) := quotientGradedMap (grading K)
  (OppositeHomogeneousQuadrics.homogeneousIdeal mu nu)

def chartQuotient (mu nu : K) : ambientAway (K := K) →+* chartRing mu nu :=
  Away.map (quotientMap mu nu) (X (4 : Fin 5))

lemma chartQuotient_surjective (mu nu : K) : Function.Surjective (chartQuotient mu nu) :=
  FourCorner.ProjectiveLocalization.away_map_surjective (quotientMap mu nu)
    (quotientGradedMap_surjective (grading K) (OppositeHomogeneousQuadrics.homogeneousIdeal mu nu))
    (Slot02HighProjSpace.X_mem_one K 4 4)

lemma dehomQuotient_T (mu nu : K) :
    dehomQuotient mu nu (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (4 : Fin 5))) = 1 := by
  simp [dehomQuotient, Ideal.quotientMap, OppositeHomogeneousQuadrics.dehomT]

/-- T evaluates to one, so actual ordinary localization and degree-zero restriction apply. -/
def chartDehom (mu nu : K) : chartRing mu nu →+* affineRing mu nu :=
  (IsLocalization.Away.lift (S := Localization.Away
    (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (4 : Fin 5))))
    _ (g := dehomQuotient mu nu) (by rw [dehomQuotient_T]; exact isUnit_one)).comp
    (algebraMap _ _)

lemma chartDehom_mk (mu nu : K) (d : ℕ) (p : coordinateRing mu nu)
    (hp : p ∈ quotientGrading mu nu (d • 1)) :
    chartDehom mu nu (Away.mk (quotientGrading mu nu)
      ((quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 4)) d p hp) =
      dehomQuotient mu nu p := by
  let t := Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (4 : Fin 5))
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
    (Slot02HighProjSpace.X_mem_one K 4 4) z
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
    ambientInverse (OppositeHomogeneousQuadrics.affineEquation mu nu i) =
      Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 4 4) 2
        (OppositeHomogeneousQuadrics.quadric mu nu i)
        (by simpa using ((mem_homogeneousSubmodule 2 _).mpr
          (OppositeHomogeneousQuadrics.quadric_homogeneous mu nu i))) := by
  apply (ambientEquiv (K := K)).injective
  change ambientDehom (ambientInverse _) = ambientDehom _
  have h := RingHom.congr_fun (ambientDehom_inverse (K := K))
    (OppositeHomogeneousQuadrics.affineEquation mu nu i)
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h, ambientDehom_mk]
  exact (OppositeHomogeneousQuadrics.dehomT_quadric mu nu i).symm

lemma chartQuotient_inverse_equation (mu nu : K) (i : Fin 3) :
    chartQuotient mu nu (ambientInverse (OppositeHomogeneousQuadrics.affineEquation mu nu i)) = 0 := by
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

/-- The actual T-chart of the three-quadric Proj equals the literal four-variable affine quotient. -/
def chartEquiv (mu nu : K) : chartRing mu nu ≃+* affineRing mu nu :=
  RingEquiv.ofRingHom (chartDehom mu nu) (chartInverse mu nu)
    (chartDehom_inverse mu nu) (chartInverse_dehom mu nu)

end FourCorner.OppositeProjective.HighChart
#print axioms FourCorner.OppositeProjective.HighChart.ambientEquiv
#print axioms FourCorner.OppositeProjective.HighChart.chartEquiv
