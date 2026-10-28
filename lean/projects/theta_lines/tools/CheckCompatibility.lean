import ThetaLinesFullAssembly
import Lean.Util.CollectAxioms
import Lean.Meta.Basic
open Lean
set_option maxRecDepth 10000
private def encodeName : Name → Json
 | .anonymous => Json.arr #[toJson "anonymous"]
 | .str p s => Json.arr #[toJson "str",encodeName p,toJson s]
 | .num p n => Json.arr #[toJson "num",encodeName p,toJson n]
private def encodeLevel : Level → Json
 | .zero => Json.arr #[toJson "zero"]
 | .succ l => Json.arr #[toJson "succ",encodeLevel l]
 | .max l k => Json.arr #[toJson "max",encodeLevel l,encodeLevel k]
 | .imax l k => Json.arr #[toJson "imax",encodeLevel l,encodeLevel k]
 | .param n => Json.arr #[toJson "param",encodeName n]
 | .mvar n => Json.arr #[toJson "mvar",toJson (toString (repr n))]
private def replaceNamePrefix (n a b : Name) : Name :=
 if n==a then b else match n with
 | .str p s => .str (replaceNamePrefix p a b) s
 | .num p i => .num (replaceNamePrefix p a b) i
 | .anonymous => .anonymous
private def normalizeName (n : Name) : Name := Id.run do
 let mut n := n
 for (a,b) in [(`_private.Mathlib.RingTheory.Flat.Rank,`_private.ThetaStdRingFlatRank),
  (`_private.Mathlib.AlgebraicGeometry.Morphisms.FlatRank,`_private.ThetaStdSchemeFlatRank),
  (`_private.Mathlib.RingTheory.Finiteness.ModuleFinitePresentation,`_private.ThetaStdModuleFinitePresentation),
  (`_private.FourCorner.ThetaBitangentAxes,`_private.ThetaBitangentAxes),
  (`_private.FourCorner.ThetaBitangentAxisIdentities,`_private.ThetaBitangentAxisIdentities),
  (`_private.FourCorner.ThetaBitangentCases,`_private.ThetaBitangentCases),
  (`_private.FourCorner.ThetaBitangentContacts,`_private.ThetaBitangentContacts),
  (`_private.FourCorner.ThetaBitangentCore,`_private.ThetaBitangentCore),
  (`_private.FourCorner.ThetaBitangentCountWave36,`_private.ThetaBitangentCountWave36),
  (`_private.FourCorner.ThetaBitangentExhaustionWave36,`_private.ThetaBitangentExhaustionWave36),
  (`_private.FourCorner.ThetaBitangentGaloisWave36,`_private.ThetaBitangentGaloisWave36),
  (`_private.FourCorner.ThetaBitangentGeneric,`_private.ThetaBitangentGeneric),
  (`_private.FourCorner.ThetaBitangentProjectiveChartsWave36,`_private.ThetaBitangentProjectiveChartsWave36),
  (`_private.FourCorner.ThetaBitangentQuadraticIndependence,`_private.ThetaBitangentQuadraticIndependence),
  (`_private.Mathlib.RingTheory.TotallySplit,`_private.ThetaStdTotallySplit)] do
  n := replaceNamePrefix n a b
 return n
private structure Dag where
 nodes : Array Json := #[]
 memo : Std.HashMap Expr Nat := {}
private partial def encodeExpr (e : Expr) : StateM Dag Nat := do
 if let some i := (←get).memo[e]? then return i
 let node ← match e with
 | .bvar i => pure (Json.arr #[toJson "bvar",toJson i])
 | .fvar i => pure (Json.arr #[toJson "fvar",toJson (toString (repr i))])
 | .mvar i => pure (Json.arr #[toJson "mvar",toJson (toString (repr i))])
 | .sort l => pure (Json.arr #[toJson "sort",encodeLevel l])
 | .const n ls => pure (Json.arr #[toJson "const",encodeName (normalizeName n),toJson (ls.map encodeLevel)])
 | .app f a => do
   let f ← encodeExpr f
   let a ← encodeExpr a
   pure (Json.arr #[toJson "app",toJson f,toJson a])
 | .lam _ t b bi => do
   let t ← encodeExpr t
   let b ← encodeExpr b
   pure (Json.arr #[toJson "lam",toJson t,toJson b,toJson (toString (repr bi))])
 | .forallE _ t b bi => do
   let t ← encodeExpr t
   let b ← encodeExpr b
   pure (Json.arr #[toJson "forall",toJson t,toJson b,toJson (toString (repr bi))])
 | .letE _ t v b nd => do
   let t ← encodeExpr t
   let v ← encodeExpr v
   let b ← encodeExpr b
   pure (Json.arr #[toJson "let",toJson t,toJson v,toJson b,toJson nd])
 | .lit (.natVal n) => pure (Json.arr #[toJson "nat",toJson n])
 | .lit (.strVal s) => pure (Json.arr #[toJson "strlit",toJson s])
 | .mdata _ e => return (←encodeExpr e)
 | .proj n i e => do
   let e ← encodeExpr e
   pure (Json.arr #[toJson "proj",encodeName (normalizeName n),toJson i,toJson e])
 let i := (←get).nodes.size
 modify fun s=>{s with nodes:=s.nodes.push node,memo:=s.memo.insert e i}
 return i

private def ja (j : Json) : Array Json := j.getArr?.toOption.get!
private def js (j : Json) : String := j.getStr?.toOption.get!
private def jn (j : Json) : Nat := j.getNat?.toOption.get!
private partial def decodeName (j : Json) : Name :=
 let a:=ja j
 match js a[0]! with
 | "anonymous" => .anonymous
 | "str" => .str (decodeName a[1]!) (js a[2]!)
 | "num" => .num (decodeName a[1]!) (jn a[2]!)
 | _ => panic! "Invalid structural Name"
private partial def decodeLevel (j : Json) : Level :=
 let a:=ja j
 match js a[0]! with
 | "zero" => .zero
 | "succ" => .succ (decodeLevel a[1]!)
 | "max" => .max (decodeLevel a[1]!) (decodeLevel a[2]!)
 | "imax" => .imax (decodeLevel a[1]!) (decodeLevel a[2]!)
 | "param" => .param (decodeName a[1]!)
 | _ => panic! "No universe metavariables allowed"
private def decodeBinder (s : String) : BinderInfo :=
 if s=="Lean.BinderInfo.default" then .default else
 if s=="Lean.BinderInfo.implicit" then .implicit else
 if s=="Lean.BinderInfo.strictImplicit" then .strictImplicit else
 if s=="Lean.BinderInfo.instImplicit" then .instImplicit else panic! "Invalid binder"
private def decodeDag (nodes : Array Json) : Array Expr := Id.run do
 let mut es := #[]
 for j in nodes do
  let a:=ja j
  let e:=match js a[0]! with
   | "bvar" => Expr.bvar (jn a[1]!)
   | "sort" => Expr.sort (decodeLevel a[1]!)
   | "const" => Expr.const (decodeName a[1]!) ((ja a[2]!).toList.map decodeLevel)
   | "app" => Expr.app es[jn a[1]!]! es[jn a[2]!]!
   | "lam" => Expr.lam .anonymous es[jn a[1]!]! es[jn a[2]!]! (decodeBinder (js a[3]!))
   | "forall" => Expr.forallE .anonymous es[jn a[1]!]! es[jn a[2]!]! (decodeBinder (js a[3]!))
   | "let" => Expr.letE .anonymous es[jn a[1]!]! es[jn a[2]!]! es[jn a[3]!]! (a[4]!.getBool?.toOption.get!)
   | "nat" => Expr.lit (.natVal (jn a[1]!))
   | "strlit" => Expr.lit (.strVal (js a[1]!))
   | "proj" => Expr.proj (decodeName a[1]!) (jn a[2]!) es[jn a[3]!]!
   | _ => panic! "Closed expressions only; no fvars or mvars"
  es:=es.push e
 return es
open Lean Elab Command Meta in
run_cmd do
 let some path ← IO.getEnv "THETA_COMPAT_PAYLOAD" | throwError "Set THETA_COMPAT_PAYLOAD to the private structural evidence JSON"
 let input ← IO.FS.readFile path
 let payload ← match Json.parse input with
  | .ok p => pure p
  | .error e => throwError "Invalid payload: {e}"
 let nodes:=ja ((payload.getObjVal? "nodes").toOption.get!)
 let es:=decodeDag nodes
 let cases:=ja ((payload.getObjVal? "cases").toOption.get!)
 for k in [:cases.size] do
  let row:=cases[k]!
  let n:=js ((row.getObjVal? "declaration").toOption.get!)
  let kind:=js ((row.getObjVal? "kind").toOption.get!)
  let root:=jn ((row.getObjVal? "root").toOption.get!)
  let declCandidates := (←getEnv).constants.toList.filter (fun entry=>entry.1.toString==n)
  unless declCandidates.length==1 do throwError "Nonunique declaration name {n}"
  let ci := declCandidates.head!.2
  let old:=es[root]!
  let new ← if kind=="type" then pure ci.type else
   match ci.value? true with
   | some e => pure e
   | none => throwError "Definition value unavailable: {n}"
  let (ty,proof) ← liftTermElabM do
   let ty ← mkEq old new
   let pf ← mkEqRefl old
   return (ty,pf)
  let certificate:=Name.str `ThetaPortableKernelCompatibility (kind++"_"++toString k)
  liftCoreM <| addDecl (.thmDecl {name:=certificate,levelParams:=ci.levelParams,type:=ty,value:=proof})
  let axioms ← collectAxioms certificate
  for ax in axioms do
   unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
    throwError "Nonstandard axiom in compatibility certificate {certificate}: {ax}"
  logInfo m!"KERNEL_RFL_CERTIFICATE {certificate} {n} {kind} {axioms.toList}"
 logInfo m!"KERNEL_RFL_CERTIFICATES {cases.size}"

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let action : StateM Dag (Array Json) := do
  let mut entries := #[]
  for (n,ci) in env.constants.toList do
   if (`ThetaPortableKernelCompatibility).isPrefixOf n then
    let ty ← encodeExpr ci.type
    let some proof := ci.value? true | panic! "Missing rfl certificate body"
    let val ← encodeExpr proof
    entries := entries.push (Json.mkObj [("declaration",toJson n.toString),
     ("level_parameters",toJson (ci.levelParams.map Name.toString)),("type",toJson ty),("value",toJson val)])
  return entries
 let (entries,dag) := action.run {}
 logInfo m!"CERTIFICATE_EXPRESSIONS {(Json.mkObj [("entries",toJson entries),("nodes",toJson dag.nodes)]).compress}"
