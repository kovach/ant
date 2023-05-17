import Std.Data.List.Basic
import DC.Syntax

instance : OfNat Value n := ⟨ .entity n ⟩

def eval (db : Data) (ctx : Configuration) : List Clause → Array Configuration
| [] => #[ctx]
| c :: cs =>
  match db.lookup c.relation with
  | none => #[]
  | some ts => Id.run do
    let mut result : Array Configuration := #[]
    for t in ts do
      let mut ctx' := some ctx
      -- assert/add bindings
      for (i, v) in c.vars.enum do
        match ctx' with
          | none => pure ()
          | some ctx =>
            match ctx.lookup v with
            | none | some none => ctx' := some $ (v, some $ t.get! i) :: ctx -- switch to push or compile into slots
            | some (some v') => if v' = t.get! i then pure () else ctx' := none
      match ctx' with
      | none => pure ()
      -- recurse
      | some ctx => for r in eval db ctx cs do result := result.push r
    pure result


def db (n : Nat) : Data :=
  [("a", [#[1,2], #[3,4]]),
   ("b", [#[1,3]]),
   ("p", List.range n |>.map fun n => #[.entity n]) ]
#eval Map.lookup (db 5) "p"

--#eval eval db (ctx := []) [⟨ "a", ["x", "y"]⟩, ⟨"b", ["x", "y"]⟩]
def q1 (n) := eval (db n) (ctx := []) [⟨ "p", ["x"]⟩, ⟨"p", ["y"]⟩] |>.size
def q1' (n) := eval (db n) (ctx := []) >> p x, p y <<
#eval q1' 10 |>.size

def main (args : List String) : IO Unit := do
  let err s := IO.println s!"please pass a number argument: {s}"
  match args with
  | x :: _ =>
    match x.toNat? with
    | some n => IO.println s!"result size:, {q1' n |>.size}!"
    | none => err 0
  | _ => err 1