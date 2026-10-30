import FamilySixMatrix08
import FamilySixKernel08

namespace FourCorner.CommonFamilyRank
open FourCorner

/-- The explicit six-prime matrix has its actual rank five over F_2. -/
theorem matrix_rank_five : commonSixMatrix.rank = 5 := by
  classical
  let f : LinearMap.ker commonSixMatrix.mulVecLin →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun e => e.val 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      funext i
      have ha := (commonSixMatrix_kernel_constants a.val).mp a.property
      have hb := (commonSixMatrix_kernel_constants b.val).mp b.property
      exact (ha i).trans (hab.trans (hb i).symm)
    · intro c
      refine ⟨⟨fun _ => c, ?_⟩, rfl⟩
      exact (commonSixMatrix_kernel_constants (fun _ => c)).mpr (fun _ => rfl)
  have hk := LinearEquiv.finrank_eq (LinearEquiv.ofBijective f hf)
  have hd := LinearMap.finrank_range_add_finrank_ker commonSixMatrix.mulVecLin
  change commonSixMatrix.rank + Module.finrank (ZMod 2) (LinearMap.ker commonSixMatrix.mulVecLin) = _ at hd
  simp only [Module.finrank_self] at hk
  rw [hk, Module.finrank_pi] at hd
  norm_num at hd
  omega

theorem prime_matrix_rank :
    (primeLegendreMatrix commonSixPrimes commonSixPrimes_prime).rank = 6-1 := by
  rw [commonSixPrimes_matrix_eq]
  exact matrix_rank_five

end FourCorner.CommonFamilyRank
#print axioms FourCorner.CommonFamilyRank.prime_matrix_rank
