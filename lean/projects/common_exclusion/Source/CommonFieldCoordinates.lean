import CommonLiteralField
noncomputable section
namespace FourCorner.CommonLiteralField
variable (K : Type*) [Field K]

def ell (t : K) : field K t := algebraMap (RatFunc K) (field K t) RatFunc.X

theorem sqP (t : K) : root K t 0 ^ 2 = ell K t + algebraMap K (field K t) (t+1) := by
  simpa only [radicand,ell, map_add, ← IsScalarTower.algebraMap_apply] using root_sq K t 0

theorem sqC (t : K) : root K t 1 ^ 2 = ell K t - algebraMap K (field K t) (t-1) := by
  simpa only [radicand,ell,map_sub,← IsScalarTower.algebraMap_apply] using root_sq K t 1

theorem sqM (t : K) : root K t 2 ^ 2 = algebraMap K (field K t) (t-1) *
    (algebraMap K (field K t) (t+1)-ell K t) / ell K t := by
  simpa only [radicand,ell,map_div₀,map_mul,map_sub,← IsScalarTower.algebraMap_apply] using root_sq K t 2

theorem sqB (t : K) : root K t 3 ^ 2 = algebraMap K (field K t) (t+1) *
    (ell K t+algebraMap K (field K t) (t-1)) / ell K t := by
  simpa only [radicand,ell,map_div₀,map_mul,map_add,← IsScalarTower.algebraMap_apply] using root_sq K t 3

theorem ell_ne_zero (t : K) : ell K t ≠ 0 := by
  exact (map_ne_zero _).mpr RatFunc.X_ne_zero
#print axioms sqM
end FourCorner.CommonLiteralField
