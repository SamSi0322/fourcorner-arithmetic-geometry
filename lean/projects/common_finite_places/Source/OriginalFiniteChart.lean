import OriginalFiniteOrders

noncomputable section
namespace FourCorner.OriginalFiniteChart
open AlgebraicCurve RadicalLinearization ResiduePlaceEvaluation OriginalFiniteOrders
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

def values {R : Type*} [CommRing R] (t l li : R) : Fin 4 → R
  | 0 => l+(t+1)
  | 1 => l-(t-1)
  | 2 => (t-1)*((t+1)-l)*li
  | 3 => (t+1)*(l+(t-1))*li

theorem map_values {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t l li : R) (i : Fin 4) :
    f (values t l li i)=values (f t) (f l) (f li) i := by
  fin_cases i <;> simp only [values,map_add,map_sub,map_mul,map_one]

theorem original_sq (i : Fin 4) :
    Genus17Geometry.fiveRoot t κ i.castSucc ^2=
      values (algebraMap k E t) (RadicalLinearization.ell k t κ)
        (RadicalLinearization.ell k t κ)⁻¹ i := by
  rw [ResidueGenerators.fiveRoot_sq]
  fin_cases i <;> simp only [CommonFiveIndependence.value,CommonLiteralField.radicand,
    values,Fin.castSucc_mk,map_add,map_sub,map_mul,map_div₀,map_inv₀,map_one,
    ← IsScalarTower.algebraMap_apply k (RatFunc k) E]
  all_goals dsimp only [RadicalLinearization.ell]
  all_goals first | rfl | ring

def originalSection (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring)
    (ha : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠0) (i : Fin 4) :
    w.toValuationSubring :=
  ⟨Genus17Geometry.fiveRoot t κ i.castSucc,
    w.mem_of_ord_nonneg (original_ne_zero h1 hm hκ i) (by
      rw [original_order h0 h1 hm hκ w hw hl i]
      simp only [ha,and_false,ite_false,sub_zero]
      split_ifs <;> norm_num)⟩

def inverseEllSection (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring)
    (ha : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠0) : w.toValuationSubring :=
  ⟨(RadicalLinearization.ell k t κ)⁻¹,inverse_mem w hw ⟨_,hl⟩ ha⟩

theorem inverse_residue (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring)
    (ha : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠0) :
    evaluate w hw (inverseEllSection w hw hl ha)=
      (evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩)⁻¹ := by
  have hh : (⟨RadicalLinearization.ell k t κ,hl⟩ : w.toValuationSubring)*inverseEllSection w hw hl ha=1 := by
    apply Subtype.ext
    exact mul_inv_cancel₀ (ell_ne_zero k t κ)
  have he := congrArg (evaluate w hw) hh
  rw [map_mul,map_one] at he
  apply mul_left_cancel₀ ha
  rw [he,mul_inv_cancel₀ ha]

theorem residue_equations (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring)
    (ha : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠0) (i : Fin 4) :
    evaluate w hw (originalSection h0 h1 hm hκ w hw hl ha i)^2=
      values t (evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩)
        (evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩)⁻¹ i := by
  have hs : originalSection h0 h1 hm hκ w hw hl ha i ^2=
      values (algebraMap k w.toValuationSubring t)
        (⟨RadicalLinearization.ell k t κ,hl⟩ : w.toValuationSubring)
        (inverseEllSection w hw hl ha) i := by
    apply Subtype.ext
    change Genus17Geometry.fiveRoot t κ i.castSucc ^2=_
    rw [original_sq]
    exact (map_values w.toValuationSubring.subtype
      (algebraMap k w.toValuationSubring t) ⟨RadicalLinearization.ell k t κ,hl⟩
      (inverseEllSection w hw hl ha) i).symm
  have he := congrArg (evaluate w hw) hs
  rw [map_pow] at he
  have hm' := map_values (evaluate w hw).toRingHom
    (algebraMap k w.toValuationSubring t) ⟨RadicalLinearization.ell k t κ,hl⟩
    (inverseEllSection w hw hl ha) i
  change (evaluate w hw) _=values ((evaluate w hw) (algebraMap k w.toValuationSubring t))
    ((evaluate w hw) ⟨RadicalLinearization.ell k t κ,hl⟩)
    ((evaluate w hw) (inverseEllSection w hw hl ha)) i at hm'
  rw [evaluate_constant,inverse_residue] at hm'
  exact he.trans hm'
end FourCorner.OriginalFiniteChart
#print axioms FourCorner.OriginalFiniteChart.residue_equations
#print axioms FourCorner.OriginalFiniteChart.original_sq
