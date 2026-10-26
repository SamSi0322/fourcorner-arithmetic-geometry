import CriticalQuotientChart
import CriticalAffineGeometry
import CriticalCharts23
import CriticalProper23

noncomputable section
namespace FourCorner.CriticalStandardCharts
open AlgebraicGeometry CategoryTheory MvPolynomial
open CriticalProj23
variable {k : Type*} [Field k]

abbrev affineEquation (i : k) (j : Fin 4) :=
  CriticalQuotientChart.affineEquation (CriticalProj23.equation i) j
abbrev affineIdeal (i : k) (j : Fin 4) :=
  CriticalQuotientChart.affineIdeal (CriticalProj23.equation i) j
abbrev affineRing (i : k) (j : Fin 4) :=
  CriticalQuotientChart.affineRing (CriticalProj23.equation i) j
instance (i : k) (j : Fin 4) : Algebra k (affineRing i j) := Ideal.Quotient.algebra k

def chartIso (i : k) (j : Fin 4) :
    (Proj.basicOpen (criticalGrading i) (coordinate i j)).toScheme ≅ Spec (.of (affineRing i j)) :=
  CriticalQuotientChart.chartSchemeIso (CriticalProj23.equation i) (equation_homogeneous i) j

theorem zero_equation (i : k) (a : Fin 2) :
    affineEquation i 0 a=CriticalAffineGeometry.equation i a := by
  fin_cases a <;> simp [affineEquation,CriticalQuotientChart.affineEquation,
    CriticalProj23.equation,F0,F1,CriticalAmbientChart.dehom,CriticalAmbientChart.drop,
    CriticalAffineGeometry.equation]

theorem zero_ideal (i : k) : affineIdeal i 0=CriticalAffineGeometry.ideal i := by
  apply congrArg Ideal.span
  exact congrArg Set.range (funext (zero_equation i))

def zeroEquiv (i : k) : affineRing i 0 ≃+* CriticalAffineGeometry.ring i :=
  Ideal.quotEquivOfEq (zero_ideal i)

def zeroChartIso (i : k) :
    (Proj.basicOpen (criticalGrading i) (coordinate i 0)).toScheme ≅
      Spec (.of (CriticalAffineGeometry.ring i)) :=
  chartIso i 0 ≪≫ Scheme.Spec.mapIso ((zeroEquiv i).symm.toCommRingCatIso.op)

end FourCorner.CriticalStandardCharts
#print axioms FourCorner.CriticalStandardCharts.chartIso
#print axioms FourCorner.CriticalStandardCharts.zeroChartIso
