import ResidueGenerators

noncomputable section
namespace FourCorner.RadicalLinearization
open Genus17Geometry

/-- Polynomial linearized radicands; the second argument is the actual
inverse-kappa coefficient, so this formula also lives in valuation rings. -/
def values {R : Type*} [CommRing R] (t ki l : R) : Fin 5 → R
  | 0 => l+(t+1)
  | 1 => l-(t-1)
  | 2 => (t-1)*((t+1)-l)*ki
  | 3 => (t+1)*(l+(t-1))*ki
  | 4 => l*ki

theorem map_values {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t ki l : R) (i : Fin 5) :
    f (values t ki l i) = values (f t) (f ki) (f l) i := by
  fin_cases i <;> simp only [values,map_add,map_sub,map_mul,map_one]

variable (k : Type*) [Field k]

abbrev ell (t κ : k) : CommonGenus17Field.field k t κ :=
  algebraMap (RatFunc k) (CommonGenus17Field.field k t κ) RatFunc.X

/-- P,C,MZ,BZ,Z are all regular over every finite ell value, including ell=0. -/
def roots (t κ : k) : Fin 5 → CommonGenus17Field.field k t κ
  | 0 => fiveRoot t κ 0
  | 1 => fiveRoot t κ 1
  | 2 => fiveRoot t κ 2 * fiveRoot t κ 4
  | 3 => fiveRoot t κ 3 * fiveRoot t κ 4
  | 4 => fiveRoot t κ 4

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ell_ne_zero (t κ : k) : ell k t κ ≠ 0 := (map_ne_zero _).mpr RatFunc.X_ne_zero

theorem ell_eq_original (t κ : k) : ell k t κ = Genus17Geometry.ell t κ := by
  rfl

/-- The five displayed linear equations hold in the ACTUAL literal field,
not in a separately labelled affine tuple or assumed normalization chart. -/
theorem roots_sq (t κ : k) (hκ : κ ≠ 0) (i : Fin 5) :
    roots k t κ i ^ 2 = values (algebraMap k (CommonGenus17Field.field k t κ) t)
      (algebraMap k (CommonGenus17Field.field k t κ) κ⁻¹) (ell k t κ) i := by
  let E := CommonGenus17Field.field k t κ
  have he : (algebraMap (RatFunc k) E RatFunc.X) ≠ 0 :=
    by simpa only [map_zero] using (algebraMap (RatFunc k) E).injective.ne RatFunc.X_ne_zero
  have hk : algebraMap k E κ ≠ 0 := by simpa only [map_zero] using (algebraMap k E).injective.ne hκ
  dsimp only [E] at he hk
  fin_cases i <;> dsimp only [roots,values]
  all_goals try rw [mul_pow]
  all_goals rw [ResidueGenerators.fiveRoot_sq]
  all_goals try rw [ResidueGenerators.fiveRoot_sq]
  all_goals simp only [CommonFiveIndependence.value,CommonLiteralField.radicand,
    map_add,map_sub,map_mul,map_div₀,map_inv₀,
    ← IsScalarTower.algebraMap_apply k (RatFunc k) (CommonGenus17Field.field k t κ),map_one]
  all_goals dsimp only [ell]
  all_goals first | rfl | (field_simp [he,hk] <;> ring)

end FourCorner.RadicalLinearization
#print axioms FourCorner.RadicalLinearization.roots_sq
#print axioms FourCorner.RadicalLinearization.ell_eq_original
