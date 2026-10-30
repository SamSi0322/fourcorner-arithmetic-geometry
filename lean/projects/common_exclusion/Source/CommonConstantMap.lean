import CommonLiteralField
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
namespace FourCorner.CommonConstantMap
open Polynomial
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The actual coefficient-extension embedding K(ell) -> L(ell). -/
def ratMap : RatFunc K →+* RatFunc L :=
  IsFractionRing.lift (K := RatFunc K)
    (g := (algebraMap L[X] (RatFunc L)).comp (Polynomial.mapRingHom (algebraMap K L)))
    ((RatFunc.algebraMap_injective (K:=L)).comp
      (Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective))

theorem ratMap_polynomial (p : K[X]) :
    ratMap K L (algebraMap K[X] (RatFunc K) p) =
      algebraMap L[X] (RatFunc L) (p.map (algebraMap K L)) :=
  IsFractionRing.lift_algebraMap _ p

theorem ratMap_X : ratMap K L RatFunc.X = RatFunc.X := by
  simpa only [RatFunc.algebraMap_X,Polynomial.map_X] using ratMap_polynomial K L Polynomial.X

theorem ratMap_constant (a : K) :
    ratMap K L (algebraMap K (RatFunc K) a) =
      algebraMap L (RatFunc L) (algebraMap K L a) := by
  change ratMap K L (RatFunc.C a) = RatFunc.C (algebraMap K L a)
  simpa only [RatFunc.algebraMap_C,Polynomial.map_C] using ratMap_polynomial K L (Polynomial.C a)

theorem radicand_map (t : K) (i : Fin 4) :
    ratMap K L (CommonLiteralField.radicand K t i) =
      CommonLiteralField.radicand L (algebraMap K L t) i := by
  fin_cases i <;>
    simp only [CommonLiteralField.radicand,map_add,map_sub,map_mul,map_div₀,map_one,
      ratMap_X,ratMap_constant]

#print axioms ratMap
#print axioms radicand_map
end FourCorner.CommonConstantMap
