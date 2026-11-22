import Lean
open Lean Elab Command

/-- Fingerprint of the statements of the given theorems and of every `GC.*` constant they
depend on (types of all, values of definitions). Printed sorted, one line per constant. -/
partial def gcClosure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then gcClosure env rest seen else
    match env.find? n with
    | none => gcClosure env rest (seen.insert n)
    | some ci =>
      let deps := ci.type.getUsedConstants.toList ++
        (match ci with
         | .defnInfo d => d.value.getUsedConstants.toList
         | .opaqueInfo d => d.value.getUsedConstants.toList
         | .inductInfo d => d.ctors
         | _ => [])
      let deps := deps.filter (fun m => (`GC).isPrefixOf m && !Meta.isMatcherCore env m &&
        !(match env.find? m with | some (.thmInfo _) => true | _ => false))
      gcClosure env (deps ++ rest) (seen.insert n)

/-- Inline auxiliary matchers (`*.match_n`), whose names depend on elaboration order. -/
partial def inlineMatchers (env : Environment) (e : Expr) : Expr :=
  e.replace fun
    | .const c ls =>
      if Meta.isMatcherCore env c then
        match env.find? c with
        | some ci@(.defnInfo _) => some (inlineMatchers env (ci.instantiateValueLevelParams! ls))
        | _ => none
      else match env.find? c with
        -- a proof inside a term: only its statement matters (proof irrelevance)
        | some ci@(.thmInfo _) =>
          some (mkApp (.const `PROOF_OF []) (inlineMatchers env (ci.instantiateTypeLevelParams ls)))
        | _ => none
    | _ => none

def fp (env : Environment) (e : Expr) : UInt64 := (inlineMatchers env e).hash

elab "#dump_stmt " ns:ident* : command => do
  let env ← getEnv
  let roots := ns.toList.map (·.getId)
  let all := (gcClosure env roots {}).toList.toArray.qsort (·.toString < ·.toString)
  for n in all do
    match env.find? n with
    | none => logInfo m!"MISSING {n}"
    | some ci =>
      let kind := match ci with
        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .axiomInfo _ => "AXIOM"
        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
      let v := match ci with
        | .defnInfo d => toString (fp env d.value) | _ => "-"
      logInfo m!"STMT {n} {kind} {fp env ci.type} {v}"
