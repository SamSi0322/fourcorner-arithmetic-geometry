import FiniteBranchCharts

noncomputable section
namespace FourCorner.InfinityRootOrders
open AlgebraicCurve AlgebraicCurve.RationalFunctionField RadicalLinearization LinearizedFactors
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ
local instance finiteLine : FiniteDimensional (RatFunc k) E := ResidueRadicalField.finite_over_line k t κ
local instance : DecidableEq (RatFunc k) := Classical.decEq _
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

theorem root_order (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring)
    (i : Fin 5) : w.ord (roots k t κ i) = -1 := by
  have he := congrArg w.ord (roots_sq_factor t κ hκ i)
  have hc : algebraMap k E (coefficient t κ i)≠0 :=
    (map_ne_zero _).mpr (coefficient_ne_zero h1 hm hκ i)
  have hf : algebraMap (RatFunc k) E (OddFourPlaces.linear (branch t i))≠0 :=
    (map_ne_zero _).mpr (OddFourPlaces.linear_ne_zero _)
  have hidx : w.ramificationIndex (RatFunc k)=2 := by
    rw [OddFiveRamification.index_formula h0 h1 hm hκ,
      ResiduePlaceImage.infinity_image t κ w hl]
    exact if_pos (Finset.mem_insert_self _ _)
  rw [show roots k t κ i ^2 = roots k t κ i ^(2:ℤ) from (zpow_ofNat _ _).symm,
    w.ord_zpow,w.ord_mul hc hf,w.ord_algebraMap,zero_add,w.ord_restrict,
    ResiduePlaceImage.infinity_image t κ w hl,OddFourPlaces.ord_linear_infty,hidx] at he
  norm_num at he
  omega

def parameter (t κ : k) : CommonGenus17Field.field k t κ := (roots k t κ 4)⁻¹
def normalized (t κ : k) (i : Fin 4) : CommonGenus17Field.field k t κ := roots k t κ i.castSucc / roots k t κ 4

theorem parameter_ne_zero (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0) : parameter t κ≠0 :=
  inv_ne_zero (roots_ne_zero h1 hm hκ 4)
theorem normalized_ne_zero (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0) (i : Fin 4) : normalized t κ i≠0 :=
  div_ne_zero (roots_ne_zero h1 hm hκ i.castSucc) (roots_ne_zero h1 hm hκ 4)

theorem parameter_order (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) :
    w.ord (parameter t κ)=1 := by
  rw [parameter,w.ord_inv,root_order h0 h1 hm hκ w hl]
  norm_num

theorem normalized_order (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) (i : Fin 4) :
    w.ord (normalized t κ i)=0 := by
  rw [normalized,QuadraticRescaledUnit.ord_div w (roots_ne_zero h1 hm hκ _) (roots_ne_zero h1 hm hκ _),
    root_order h0 h1 hm hκ w hl,root_order h0 h1 hm hκ w hl,sub_self]

/-- The normalized coordinates retain the original ordered M and B exactly. -/
theorem normalized_original (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0) :
    normalized t κ 0=Genus17Geometry.fiveRoot t κ 0/Genus17Geometry.fiveRoot t κ 4 ∧
    normalized t κ 1=Genus17Geometry.fiveRoot t κ 1/Genus17Geometry.fiveRoot t κ 4 ∧
    normalized t κ 2=Genus17Geometry.fiveRoot t κ 2 ∧
    normalized t κ 3=Genus17Geometry.fiveRoot t κ 3 := by
  have hz : Genus17Geometry.fiveRoot t κ 4≠0 := roots_ne_zero h1 hm hκ 4
  simp only [normalized,roots,Fin.castSucc_mk,Fin.reduceFinMk]
  exact ⟨rfl,rfl,mul_div_cancel_right₀ _ hz,mul_div_cancel_right₀ _ hz⟩
end FourCorner.InfinityRootOrders
#print axioms FourCorner.InfinityRootOrders.root_order
#print axioms FourCorner.InfinityRootOrders.normalized_original
#print axioms FourCorner.InfinityRootOrders.parameter_order
#print axioms FourCorner.InfinityRootOrders.normalized_order
