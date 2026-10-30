import ThetaCoverClassPortable.InvertibleRationalFiber

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
namespace FourCorner.LineIsoDescent

def descendUnitIso {X Y : Scheme} (j : X ≅ Y) (M : Y.Modules)
    (e : (Scheme.Modules.pullback j.hom).obj M ≅ 𝟙_ X.Modules) : M ≅ 𝟙_ Y.Modules :=
  ((Scheme.Modules.pullbackId Y).app M).symm ≪≫
    ((Scheme.Modules.pullbackCongr j.inv_hom_id).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp j.inv j.hom).app M).symm ≪≫
    (Scheme.Modules.pullback j.inv).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso j.inv

#print axioms descendUnitIso
end FourCorner.LineIsoDescent
