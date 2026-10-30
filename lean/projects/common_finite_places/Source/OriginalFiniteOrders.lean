import InfinityRootOrders

noncomputable section
namespace FourCorner.OriginalFiniteOrders
open AlgebraicCurve RadicalLinearization ResiduePlaceEvaluation LinearizedFactors InfinityRootOrders
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ
attribute [local instance] Classical.propDecidable

theorem original_ne_zero (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0) (i : Fin 4) :
    Genus17Geometry.fiveRoot t κ i.castSucc≠0 := by
  have hn := roots_ne_zero h1 hm hκ i.castSucc
  fin_cases i <;> simp only [roots,Fin.castSucc_mk] at hn ⊢
  · exact hn
  · exact hn
  · exact (mul_ne_zero_iff.mp hn).1
  · exact (mul_ne_zero_iff.mp hn).1

theorem original_order (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring) (i : Fin 4) :
    w.ord (Genus17Geometry.fiveRoot t κ i.castSucc)=
      (if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t i.castSucc then 1 else 0)-
      (if (2 : ℕ) ≤ i.val ∧ evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=0 then 1 else 0) := by
  have hro := FiniteRootData.root_order h0 h1 hm hκ w hw hl i.castSucc
  have hzo := FiniteRootData.root_order h0 h1 hm hκ w hw hl 4
  have hmult (j : Fin 4) :
      w.ord (Genus17Geometry.fiveRoot t κ j.castSucc*roots k t κ 4)=
      w.ord (Genus17Geometry.fiveRoot t κ j.castSucc)+w.ord (roots k t κ 4) :=
    w.ord_mul (original_ne_zero h1 hm hκ j) (roots_ne_zero h1 hm hκ 4)
  fin_cases i <;> simp only [Fin.castSucc_mk,Fin.reduceFinMk,branch,roots] at hro hzo ⊢
  · simpa using hro
  · simpa using hro
  · have hh := hmult 2
    change w.ord (roots k t κ 2)=_ at hh
    rw [FiniteRootData.root_order h0 h1 hm hκ w hw hl 2,
      FiniteRootData.root_order h0 h1 hm hκ w hw hl 4] at hh
    simp only [branch] at hh
    simp only [le_refl,true_and]
    change w.ord (Genus17Geometry.fiveRoot t κ 2) =
      (if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=t+1 then 1 else 0)-
      (if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=0 then 1 else 0)
    change (if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=t+1 then 1 else 0) =
      w.ord (Genus17Geometry.fiveRoot t κ 2)+(if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=0 then 1 else 0) at hh
    omega
  · have hh := hmult 3
    change w.ord (roots k t κ 3)=_ at hh
    rw [FiniteRootData.root_order h0 h1 hm hκ w hw hl 3,
      FiniteRootData.root_order h0 h1 hm hκ w hw hl 4] at hh
    simp only [branch] at hh
    simp only [show 2 ≤ (3:ℕ) by omega,true_and]
    change w.ord (Genus17Geometry.fiveRoot t κ 3) =
      (if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩= -(t-1) then 1 else 0)-
      (if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=0 then 1 else 0)
    change (if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩= -(t-1) then 1 else 0) =
      w.ord (Genus17Geometry.fiveRoot t κ 3)+(if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=0 then 1 else 0) at hh
    omega

theorem zero_poles (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring)
    (ha : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=0) :
    w.ord (Genus17Geometry.fiveRoot t κ 2) = -1 ∧
    w.ord (Genus17Geometry.fiveRoot t κ 3) = -1 := by
  have hs : t-1≠0 := sub_ne_zero.mpr h1
  have hT : t+1≠0 := by intro h; apply hm; linear_combination h
  have hM := original_order h0 h1 hm hκ w hw hl 2
  have hB := original_order h0 h1 hm hκ w hw hl 3
  simp only [Fin.castSucc_mk,branch,ha] at hM hB
  have hsn : (0:k)≠1-t := by intro h; apply h1; linear_combination h
  simpa [Ne.symm hT,hs,hsn] using And.intro hM hB
end FourCorner.OriginalFiniteOrders
#print axioms FourCorner.OriginalFiniteOrders.original_order
#print axioms FourCorner.OriginalFiniteOrders.zero_poles
