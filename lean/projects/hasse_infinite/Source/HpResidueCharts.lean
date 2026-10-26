import HpFiniteBaseGenus
import ResiduePlaceEvaluation

namespace FourCorner.HpResidueCharts

open AlgebraicCurve HpLiteralField HpFieldGeometry ResiduePlaceEvaluation
noncomputable section

def values {R : Type*} [CommRing R] (p rho : R) : Fin 4 → R
  | 0 => p*rho
  | 1 => 2*(p-1)*(rho-1)
  | 2 => 2*(p+1)*(rho+1)
  | 3 => (p-1)*rho+p+1

theorem map_values {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p rho : R) (i : Fin 4) :
    f (values p rho i)=values (f p) (f rho) i := by
  fin_cases i <;> simp only [values,map_mul,map_sub,map_add,map_ofNat,map_one]

def infinityValues {R : Type*} [CommRing R] (p pinv h : R) : Fin 3 → R
  | 0 => 2*(p-1)*pinv*(1-h)
  | 1 => 2*(p+1)*pinv*(1+h)
  | 2 => (p-1)*pinv+(p+1)*pinv*h

theorem map_infinityValues {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p pinv h : R) (i : Fin 3) :
    f (infinityValues p pinv h i)=infinityValues (f p) (f pinv) (f h) i := by
  fin_cases i <;> simp only [infinityValues,map_mul,map_sub,map_add,map_ofNat,map_one]

variable (K : Type*) [Field K]

def rho (p : K) : field K p := algebraMap (RatFunc K) (field K p) RatFunc.X

theorem rho_ne_zero (p : K) : rho K p ≠ 0 := (map_ne_zero _).mpr RatFunc.X_ne_zero

theorem root_sq_values (p : K) (i : Fin 4) :
    root K p i^2=values (algebraMap K (field K p) p) (rho K p) i := by
  rw [root_sq]
  fin_cases i <;> simp only [radicand,poly,values,rho,map_mul,map_sub,map_add,map_one,map_ofNat,
    RatFunc.algebraMap_X,RatFunc.algebraMap_C,← RatFunc.algebraMap_eq_C,
    ← IsScalarTower.algebraMap_apply K (RatFunc K) (field K p)] <;> ring

theorem root_zero_ne_zero (p : K) (hp : p ≠ 0) : root K p 0 ≠ 0 := by
  intro hz
  have hh := root_sq_values K p 0
  change root K p 0^2=algebraMap K (field K p) p*rho K p at hh
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at hh
  exact (mul_ne_zero ((map_ne_zero _).mpr hp) (rho_ne_zero K p)) hh.symm

def normalized (p : K) (i : Fin 3) : field K p := root K p i.succ/root K p 0

theorem normalized_sq (p : K) (hp : p ≠ 0) (i : Fin 3) :
    normalized K p i^2=infinityValues (algebraMap K (field K p) p)
      (algebraMap K (field K p) p⁻¹) (rho K p)⁻¹ i := by
  have hp' : algebraMap K (field K p) p ≠ 0 := (map_ne_zero _).mpr hp
  rw [normalized,div_pow,root_sq_values,root_sq_values,map_inv₀]
  let P := algebraMap K (field K p) p
  let x := rho K p
  have hP0 : P ≠ 0 := hp'
  have hx0 : x ≠ 0 := rho_ne_zero K p
  fin_cases i
  · change (2*(P-1)*(x-1))/(P*x)=2*(P-1)*P⁻¹*(1-x⁻¹)
    field_simp [hP0,hx0] <;> ring
  · change (2*(P+1)*(x+1))/(P*x)=2*(P+1)*P⁻¹*(1+x⁻¹)
    field_simp [hP0,hx0] <;> ring
  · change ((P-1)*x+P+1)/(P*x)=(P-1)*P⁻¹+(P+1)*P⁻¹*x⁻¹
    field_simp [hP0,hx0] <;> ring

/-- A finite parameter at the SAME actual rational place gives the four
residue roots, including every finite branch point and every zero root. -/
theorem finite_chart (p : K) (w : Place K (field K p)) (hw : w.IsRational)
    (hrho : rho K p∈w.toValuationSubring) :
    ∃ a : K,∃ r : Fin 4 → K,∀i,r i^2=values p a i := by
  let R : w.toValuationSubring := ⟨rho K p,hrho⟩
  let rhs (i : Fin 4) := values (algebraMap K w.toValuationSubring p) R i
  have hco (i : Fin 4) : (rhs i : field K p)=values (algebraMap K (field K p) p) (rho K p) i := by
    exact map_values w.toValuationSubring.subtype _ _ i
  let r (i : Fin 4) : w.toValuationSubring :=
    ⟨root K p i,root_mem w ((hco i) ▸ (rhs i).property) (root_sq_values K p i)⟩
  have hs (i : Fin 4) : r i^2=rhs i := by
    apply Subtype.ext
    exact (root_sq_values K p i).trans (hco i).symm
  refine ⟨evaluate w hw R,fun i => evaluate w hw (r i),?_⟩
  intro i
  have hh := congrArg (evaluate w hw) (hs i)
  rw [map_pow] at hh
  have hm := map_values (evaluate w hw).toRingHom (algebraMap K w.toValuationSubring p) R i
  change (evaluate w hw) _=values ((evaluate w hw) (algebraMap K w.toValuationSubring p))
    ((evaluate w hw) R) i at hm
  rw [evaluate_constant] at hm
  exact hh.trans hm

/-- Every point above infinity is retained: normalize by the actual first
root, whose squared value is p*rho, and evaluate its three regular ratios. -/
theorem infinity_chart (p : K) (hp : p ≠ 0) (w : Place K (field K p)) (hw : w.IsRational)
    (hrho : rho K p∉w.toValuationSubring) :
    ∃ r : Fin 3 → K,∀i,r i^2=infinityValues p p⁻¹ 0 i := by
  obtain ⟨H,hH,hzero⟩ := pole_inverse w hw hrho
  let rhs (i : Fin 3) := infinityValues (algebraMap K w.toValuationSubring p)
    (algebraMap K w.toValuationSubring p⁻¹) H i
  have hco (i : Fin 3) : (rhs i : field K p)=infinityValues (algebraMap K (field K p) p)
      (algebraMap K (field K p) p⁻¹) (rho K p)⁻¹ i := by
    have hh := map_infinityValues w.toValuationSubring.subtype
      (algebraMap K w.toValuationSubring p) (algebraMap K w.toValuationSubring p⁻¹) H i
    change (rhs i : field K p)=infinityValues (algebraMap K (field K p) p)
      (algebraMap K (field K p) p⁻¹) (H : field K p) i at hh
    rwa [hH] at hh
  let r (i : Fin 3) : w.toValuationSubring :=
    ⟨normalized K p i,root_mem w ((hco i) ▸ (rhs i).property) (normalized_sq K p hp i)⟩
  have hs (i : Fin 3) : r i^2=rhs i := by
    apply Subtype.ext
    exact (normalized_sq K p hp i).trans (hco i).symm
  refine ⟨fun i => evaluate w hw (r i),?_⟩
  intro i
  have hh := congrArg (evaluate w hw) (hs i)
  rw [map_pow] at hh
  have hm := map_infinityValues (evaluate w hw).toRingHom
    (algebraMap K w.toValuationSubring p) (algebraMap K w.toValuationSubring p⁻¹) H i
  change (evaluate w hw) _=infinityValues ((evaluate w hw) (algebraMap K w.toValuationSubring p))
    ((evaluate w hw) (algebraMap K w.toValuationSubring p⁻¹)) ((evaluate w hw) H) i at hm
  rw [evaluate_constant,evaluate_constant,hzero] at hm
  exact hh.trans hm

/-- Exhaustive same-place finite/branch/infinity residue charts. No affine
chart or nonzero residue parameter is assumed. -/
theorem exhaustive_charts (p : K) (hp : p ≠ 0) (w : Place K (field K p)) (hw : w.IsRational) :
    (∃ a : K,∃ r : Fin 4 → K,∀i,r i^2=values p a i) ∨
      (∃ r : Fin 3 → K,∀i,r i^2=infinityValues p p⁻¹ 0 i) := by
  by_cases hrho : rho K p∈w.toValuationSubring
  · exact Or.inl (finite_chart K p w hw hrho)
  · exact Or.inr (infinity_chart K p hp w hw hrho)

#print axioms root_sq_values
#print axioms normalized_sq
#print axioms finite_chart
#print axioms infinity_chart
#print axioms exhaustive_charts

end
end FourCorner.HpResidueCharts
