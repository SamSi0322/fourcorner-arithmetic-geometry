import DescentAlgebra
import Lean.Util.CollectAxioms

#check @FourCorner.FiniteWidePullback.exists_good_limit
#print axioms FourCorner.FiniteWidePullback.exists_good_limit
#check @FourCorner.FiniteWidePullback.fin_base
#print axioms FourCorner.FiniteWidePullback.fin_base
#check @CategoryTheory.MorphismProperty.widePullback_base
#print axioms CategoryTheory.MorphismProperty.widePullback_base
#check @FourCorner.FiniteWidePullback.scheme_fibre_power
#print axioms FourCorner.FiniteWidePullback.scheme_fibre_power
#check @FourCorner.FiniteWidePullback.proper_scheme_fibre_power
#print axioms FourCorner.FiniteWidePullback.proper_scheme_fibre_power
#check @FourCorner.FiniteWidePullback.affine_scheme_fibre_power
#print axioms FourCorner.FiniteWidePullback.affine_scheme_fibre_power
#check @FourCorner.PairCoactionInvariants.coefficient
#print axioms FourCorner.PairCoactionInvariants.coefficient
#check @FourCorner.PairCoactionInvariants.coefficient_tmul
#print axioms FourCorner.PairCoactionInvariants.coefficient_tmul
#check @FourCorner.PairCoactionInvariants.coefficient_natural
#print axioms FourCorner.PairCoactionInvariants.coefficient_natural
#check @FourCorner.PairCoactionInvariants.exists_nonzero_coefficient
#print axioms FourCorner.PairCoactionInvariants.exists_nonzero_coefficient
#check @FourCorner.PairCoactionInvariants.unitVector
#print axioms FourCorner.PairCoactionInvariants.unitVector
#check @FourCorner.PairCoactionInvariants.coefficient_invariant
#print axioms FourCorner.PairCoactionInvariants.coefficient_invariant
#check @FourCorner.PairCoactionInvariants.exists_nonzero_invariant_of_injective
#print axioms FourCorner.PairCoactionInvariants.exists_nonzero_invariant_of_injective
#check @FourCorner.PairCoactionInvariants.exists_nonzero_invariant_of_counit
#print axioms FourCorner.PairCoactionInvariants.exists_nonzero_invariant_of_counit
#check @FourCorner.IdealFlatDescent.tensor_kernel_of_flat
#print axioms FourCorner.IdealFlatDescent.tensor_kernel_of_flat
#check @FourCorner.IdealFlatDescent.map_comap_of_tensor_invariance
#print axioms FourCorner.IdealFlatDescent.map_comap_of_tensor_invariance
#check @Ideal.map_comap_eq_self_of_map_includeLeft_eq_map_includeRight
#print axioms Ideal.map_comap_eq_self_of_map_includeLeft_eq_map_includeRight
#check @FourCorner.IdealFlatDescent.affine_global_sections_faithfully_flat
#print axioms FourCorner.IdealFlatDescent.affine_global_sections_faithfully_flat
#check @FourCorner.IdealFlatDescent.affine_ideal_descends
#print axioms FourCorner.IdealFlatDescent.affine_ideal_descends
#check @Module.finitePresentation_of_rankAtStalk_eq
#print axioms Module.finitePresentation_of_rankAtStalk_eq
#check @FourCorner.ModuleLocalizedRank.tensorEquivOfLocalizedEquiv
#print axioms FourCorner.ModuleLocalizedRank.tensorEquivOfLocalizedEquiv
#check @FourCorner.ModuleLocalizedRank.tensorPiLocalization
#print axioms FourCorner.ModuleLocalizedRank.tensorPiLocalization
#check @FourCorner.ModuleLocalizedRank.scalarTensorEquiv
#print axioms FourCorner.ModuleLocalizedRank.scalarTensorEquiv
#check @FourCorner.ModuleLocalizedRank.rankAtMaximal_eq_of_localizedEquiv
#print axioms FourCorner.ModuleLocalizedRank.rankAtMaximal_eq_of_localizedEquiv
#check @Module.rankAtStalk_eq_of_forall_localizedModule_equiv
#print axioms Module.rankAtStalk_eq_of_forall_localizedModule_equiv

private def canonicalType : Lean.Expr → Lean.Expr
 | .forallE _ d b bi => .forallE .anonymous (canonicalType d) (canonicalType b) bi
 | .lam _ d b bi => .lam .anonymous (canonicalType d) (canonicalType b) bi
 | .letE _ t v b nd => .letE .anonymous (canonicalType t) (canonicalType v) (canonicalType b) nd
 | .app f a => .app (canonicalType f) (canonicalType a)
 | .mdata _ e => canonicalType e
 | .proj n i e => .proj n i (canonicalType e)
 | e => e

open Lean Elab Command in
run_cmd do
 let env ←getEnv
 let owned := #[`FiniteWidePullback,
   `Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base,
   `WidePullbackSchemeApplications,
   `PairCoactionInvariants,
   `FlatTensorKernel,
   `IdealFlatDescent,
   `IdealTensorDescent,
   `AffineIdealDescent,
   `Theorems.Thm_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight,
   `ModuleConstantRankPresentation,
   `ModuleLocalizedRank,
   `Theorems.Thm_Module_rankAtStalk_eq_of_forall_localizedModule_equiv,
   `Theorems.Thm_Module_finitePresentation_of_rankAtStalk_eq]
 let allowed := #[`propext,`Classical.choice,`Quot.sound]
 let mut count : Nat := 0
 for (n,_) in env.constants.toList do
  if let some idx:=env.getModuleIdxFor? n then
   if owned.contains env.header.moduleNames[idx.toNat]! then
    let ax ←collectAxioms n
    for a in ax do
     unless allowed.contains a do throwError "Nonstandard axiom {a} in {n}"
    count:=count+1
 logInfo m!"AUDIT_DECLARATIONS {count}"
 let api := #[`FourCorner.FiniteWidePullback.exists_good_limit,
   `FourCorner.FiniteWidePullback.fin_base,
   `CategoryTheory.MorphismProperty.widePullback_base,
   `FourCorner.FiniteWidePullback.scheme_fibre_power,
   `FourCorner.FiniteWidePullback.proper_scheme_fibre_power,
   `FourCorner.FiniteWidePullback.affine_scheme_fibre_power,
   `FourCorner.PairCoactionInvariants.coefficient,
   `FourCorner.PairCoactionInvariants.coefficient_tmul,
   `FourCorner.PairCoactionInvariants.coefficient_natural,
   `FourCorner.PairCoactionInvariants.exists_nonzero_coefficient,
   `FourCorner.PairCoactionInvariants.unitVector,
   `FourCorner.PairCoactionInvariants.coefficient_invariant,
   `FourCorner.PairCoactionInvariants.exists_nonzero_invariant_of_injective,
   `FourCorner.PairCoactionInvariants.exists_nonzero_invariant_of_counit,
   `FourCorner.IdealFlatDescent.tensor_kernel_of_flat,
   `FourCorner.IdealFlatDescent.map_comap_of_tensor_invariance,
   `Ideal.map_comap_eq_self_of_map_includeLeft_eq_map_includeRight,
   `FourCorner.IdealFlatDescent.affine_global_sections_faithfully_flat,
   `FourCorner.IdealFlatDescent.affine_ideal_descends,
   `Module.finitePresentation_of_rankAtStalk_eq,
   `FourCorner.ModuleLocalizedRank.tensorEquivOfLocalizedEquiv,
   `FourCorner.ModuleLocalizedRank.tensorPiLocalization,
   `FourCorner.ModuleLocalizedRank.scalarTensorEquiv,
   `FourCorner.ModuleLocalizedRank.rankAtMaximal_eq_of_localizedEquiv,
   `Module.rankAtStalk_eq_of_forall_localizedModule_equiv]
 for n in api do
  let ci ←getConstInfo n
  let payload:=Json.mkObj [("declaration",toJson n.toString),("level_parameters",toJson (ci.levelParams.map Name.toString)),("kernel_type",toJson (toString (repr (canonicalType ci.type))))]
  logInfo m!"TYPE_PIN {payload.compress}"
