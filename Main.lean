import Std.Data.List.Basic
import Std.Data.HashMap
import DC.Syntax

open Std (AssocList HashMap)

instance : OfNat Value n := ⟨ .entity n ⟩

def eval_aux (db : Data) (ctx : Configuration) (acc : Array Configuration) : List Clause → Array Configuration
| [] => acc.push ctx
| c :: cs =>
  match db.find? c.relation with
  | none => #[]
  | some ts => Id.run do
    let mut results := acc
    for t in ts do
      let mut ctx' := some ctx
      -- assert/add bindings
      for (i, v) in c.vars.enum do
        match ctx' with
          | none => pure ()
          | some ctx =>
            match ctx.lookup v with
            | none | some none => ctx' := some  $ ctx.cons v (some $ t.2.get! i)
            | some (some v') => if v' = t.2.get! i then pure () else ctx' := none
      match ctx' with
      | none => pure ()
      -- recurse
      | some ctx => results := eval_aux db ctx results cs
    pure results

def eval (db : Data) (ctx : Configuration) : List Clause → Array Configuration := eval_aux db ctx #[]

open Std (AssocList)

def Clause.subst (config : DefiniteConfiguration) (c : Clause) : Tuple :=
  ⟨ c.relation, c.vars.map config.lookup! |>.toArray ⟩

def doEffect (ctr : Nat) (config : DefiniteConfiguration) (new : List Var)
    (effect : List Clause) : Nat × List Tuple :=
  let config := new.foldr (init := (ctr, config)) fun v (n, config) => (n+1, config.cons v (.entity n))
  (config.1, effect.map (Clause.subst config.2))

def Data.insert : Data → Tuple → Data := fun d t =>
  d.modify t.relation fun _ v => v.push t

def World.effect (w : World) (new : List Var) (effect : List Clause)
    (config : DefiniteConfiguration) : World :=
  let (n, tuples) := doEffect w.counter config new effect
  {counter := n, tuples := tuples.foldl (init := w.tuples) Data.insert}

def Configuration.toDefinite : Configuration → DefiniteConfiguration :=
fun c => c.mapVal fun _ v => v.get!


def db (n : Nat) : Data :=
  HashMap.ofList [ ("p", Array.range n |>.map fun n => ⟨"p", #[.entity n]⟩) ]

--#eval eval db (ctx := []) [⟨ "a", ["x", "y"]⟩, ⟨"b", ["x", "y"]⟩]
def q1 (n) := eval (db n) (ctx := {}) [⟨ "p", ["x"]⟩, ⟨"p", ["y"]⟩] |>.size
def q1' (n) := eval (db n) (ctx := {}) (>> p x, p y <<).clauses
#eval q1' 10 |>.size

def main (args : List String) : IO Unit := do
  let err s := IO.println s!"please pass a number argument: {s}"
  match args with
  | x :: _ =>
    match x.toNat? with
    | some n => IO.println s!"result size:, {q1' n |>.size}!"
    | none => err 0
  | _ => err 1

#eval >> p x y, q y x <<


-- fix identifier limitation
-- try calling Lean on a text file?
-- event pre / match / post