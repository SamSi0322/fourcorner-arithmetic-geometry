import FiniteNormalizationCover
import CommonActualGenus

noncomputable section
open AlgebraicCurve IsDedekindDomain
namespace FourCorner.NormalizationPlaceRestriction
universe u
variable {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E]

/-- Contraction of an actual height-one prime under a coefficient-compatible normalization
ring map agrees with genuine restriction of its function-field place. -/
theorem heightOne_restrict (A : Subalgebra K F) (B : Subalgebra K E)
    [IsDedekindDomain A] [IsDedekindDomain B] [IsFractionRing A F] [IsFractionRing B E]
    (f : A →+* B) (hf : ∀ a : A, (f a : E) = algebraMap F E (a : F))
    (q : HeightOneSpectrum A) (p : HeightOneSpectrum B)
    (hcomap : q.asIdeal = Ideal.comap f p.asIdeal) :
    (Place.ofHeightOneSpectrum (K := K) (F := E) p).restrict F = Place.ofHeightOneSpectrum (K := K) (F := F) q := by
  let w := Place.ofHeightOneSpectrum (K := K) (F := E) p
  let v := Place.ofHeightOneSpectrum (K := K) (F := F) q
  have hle : v.toValuationSubring ≤ (w.restrict F).toValuationSubring := by
    intro x hx
    change x ∈ (Place.ofHeightOneSpectrum (K := K) (F := F) q).toValuationSubring at hx
    rw [Place.ofHeightOneSpectrum_toValuationSubring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hx
    obtain ⟨a,b,hb,rfl⟩ := hx
    rw [Place.restrict_toValuationSubring,ValuationSubring.mem_comap]
    change algebraMap F E ((a:F)*(b:F)⁻¹) ∈ (Place.ofHeightOneSpectrum (K := K) (F := E) p).toValuationSubring
    rw [Place.ofHeightOneSpectrum_toValuationSubring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    refine ⟨f a,f b,?_,?_⟩
    · intro hm
      exact hb (by rw [hcomap]; exact hm)
    · rw [map_mul,map_inv₀]
      change algebraMap F E (a:F)*(algebraMap F E (b:F))⁻¹ = (f a:E)*(f b:E)⁻¹
      rw [hf,hf]
  exact (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle (w.restrict F).ne_top')).symm

end FourCorner.NormalizationPlaceRestriction
#print axioms FourCorner.NormalizationPlaceRestriction.heightOne_restrict
