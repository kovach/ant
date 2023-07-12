import Std.Data.List.Basic
import Std.Data.HashMap
import Ant.Basic

namespace Ant

open Std (AssocList HashMap)

def eval_aux' (db : Data) (ctx : Binding) (acc : Array Binding) (k : Binding → Array Binding → List Atom → Array Binding)
    : Atom → List Atom → Array Binding
| c, cs =>
  match db.find? c.relation with
  | none => #[]
  | some ⟨ts⟩ => Id.run do
    let mut results := acc
    for t in ts do
      let mut ctx' := some ctx
      -- assert/add bindings
      for (i, v) in c.vars.enum do
        match ctx' with
          | none => pure ()
          | some ctx =>
            match v with
            | .var name =>
              match v.eval? ctx with
              | none => ctx' := some  $ ctx.cons name (t.2.get! i)
              | some v' => if v' = t.2.get! i then pure () else ctx' := none
            | _ => let v' := v.eval ctx; if v' = t.2.get! i then pure () else ctx' := none
      match ctx' with
      | none => pure ()
      -- recurse
      | some ctx => results := k ctx results cs
    pure results

-- todo remove?
def eval_aux (db : Data) (ctx : Binding) (acc : Array Binding)
    : List Atom → Array Binding
| [] => acc.push ctx
| c :: cs =>
  match db.find? c.relation with
  | none => #[]
  | some ⟨ts⟩ => Id.run do
    let mut results := acc
    for t in ts do
      let mut ctx' := some ctx
      -- assert/add bindings
      for (i, v) in c.vars.enum do
        match ctx' with
          | none => pure ()
          | some ctx =>
            match v with
            | .var name =>
              match v.eval? ctx with
              | none => ctx' := some  $ ctx.cons name (t.2.get! i)
              | some v' => if v' = t.2.get! i then pure () else ctx' := none
            | _ => let v' := v.eval ctx; if v' = t.2.get! i then pure () else ctx' := none
      match ctx' with
      | none => pure ()
      -- recurse
      | some ctx => results := eval_aux db ctx results cs
    pure results

-- returns all matches (once) that involve at least one tuple from `new`
partial def seminaive (old new total : Data) (ctx : Binding) (acc : Array Binding) : List Atom → Array Binding
| [] => acc -- never matched new tuple, current ctx invalid
| [c] => -- small optimization
  -- must match new tuple
  eval_aux new ctx acc [c]
| c :: cs =>
  --      must match new tuple, may match any tuples in remainder
  let matchNewNow   temp := eval_aux' new ctx temp (eval_aux total) c cs
  -- (or) must match old tuple, must match a new tuple in the remainder
  let matchNewLater temp := eval_aux' old ctx temp (seminaive old new total) c cs
  acc |> matchNewNow |> matchNewLater

def eval (db : Data) (ctx : Binding) : List Atom → Array Binding := eval_aux db ctx #[]
def seminaive_eval (old new total : Data) (ctx : Binding) : List Atom → Array Binding := seminaive old new total ctx #[]

-- todo: simultaneous
inductive C | seq | chosenSeq | chooseOne

instance : ToString C where
  toString
  | .seq => "seq"
  | .chosenSeq => "chosenSeq"
  | .chooseOne => "choose"

instance C.Inhabited : Inhabited C := ⟨.seq⟩

abbrev Delta := Frame
abbrev Time := Frame × Delta
abbrev Guard := List Atom
abbrev Rule := String × Guard × Query
abbrev Program := List Rule

abbrev M := StateM Nat
def fresh : M Id := modifyGet fun s => (s, s+1)
def freshStr : M String := do let n ← fresh; pure s!"v{n}"

inductive State
| node    (type : C) (focus : Option State) (now : Frame) (children : Array State)
| new     (type : C) (delta : Frame)
| query   (n : String) (ctx : Binding) (q : Query)
| invalid (error : String) (cause : State)
| nil
deriving Inhabited

partial def State.pp (s : State) : String :=
  match s with
  | node t none f cs => s!"(node {t} none {f} {cs.map State.pp})"
  | node t focus f cs =>
    let x := match focus with | none =>  "" | some v => s!"{v.pp} "
    s!"(node {t} {x} {f} {cs.map State.pp})"
  | new _ f => s!"(new {f})"
  | query name .. => s!"(query {name})"
  | nil => "nil"
  | invalid msg s => s!"\n\n\n(invalid ({msg}): {s.pp})\n\n\n"

inductive Choice | index (n : ℕ)

def newVars (config : Binding) (new : List Var) : M Binding :=
  let cause := config.toCause
  new.foldlM (init := config) fun ctx v => do { let e ← fresh; pure $ ctx.cons v (.entity e cause) }

def State.terminal : State → Bool
| node _ none _ cs => cs.size == 0
| query _ _ .nil => true
| _ => false

-- only valid for terminal States
partial def State.frame : State → Frame
| node _ none f _ => f
-- | node /-todo?-/ _ cs => cs.map State.frame |>.foldl Frame.append {}
| _ => {}

def doEffect
    (name : String) (new : List Var) (free : List Var) (value : List Atom) (cont : Query)
    (ctx : Binding) (w : Frame) : M State := do
  let ctx' ← newVars ctx new
  let created := doNewTuples ctx' value
  let freed := free.filterMap fun v => match ctx.find! v with | .entity n _ => some n | _ => panic! s!"type error: [{v}] refers to non-entity" -- hmm
  let newNode : State := .new default ⟨Data.ofTuples created, freed.toArray⟩
  let node : State := .node .seq none w #[.query name ctx' cont, newNode]
  pure node

def State.advance (p : Program) (w : Frame) : State → M State
| s@(node .seq none w' cs) => pure $ match cs.back? with
  | none => invalid "internal error" s -- should match higher level
  | some v => .node .seq (some v) w' cs.pop
| node t (some s) w' s' =>
  if s.terminal then pure $ node t none (w' ++ s.frame) s'
  else do pure $ node t (some (← s.advance p w')) w' s'
| new type delta =>
  let now := w ++ delta
  let states : Array State := List.foldl Array.append #[] $
    p.map fun (name, guard, q) => (eval_aux delta.tuples {} #[] guard).map fun ctx => query name ctx q
  pure $ node type none now states.reverse
| s@(query name ctx q) =>
  match q with
  | .nil => pure $ .invalid "cannot advance nil query" s
  | .effect n f atoms k => doEffect name n f atoms k ctx w
  | .step type q qs => pure $
    let nodes : Array State := eval w.tuples ctx q |>.map fun b => .query name b qs
    match type with
    | .all => node .seq none w nodes -- todo, use chosenSeq
    | .chooseOne => node .chooseOne none w nodes
| s => pure $ invalid "cannot advance" s

def State.nextChoice : State → Option (Array State)
| node _ none _ cs => some cs
| node _ (some c) _ _ => c.nextChoice
| _ => none

def State.applyChoice (k : Nat) : State → State
| node type none f cs =>
   match cs.splitAt' k with
   | (pre, some c, post) =>
     match type with
     | .chosenSeq => node .chosenSeq none f (pre ++ post)
     | .chooseOne => c
     | .seq => panic! "cannot choose order of this node"
    | _ => panic! "invalid choice index"
| node type (some c) f cs => node type (some $ c.applyChoice k) f cs
| _ => panic! "internal error applyChoice"

def State.advanceFix (p : Program) (w : Frame) : Nat → State → M State
| 0, s => pure s
| n+1, s => do
  match (← s.advance p w) with
  | invalid .. => pure s
  | s' => s'.advanceFix p w n

def db (n : Nat) : Data := Data.ofTuples $
  List.range n |>.map fun n => ⟨"p", #[.entity n []]⟩

def q_ (n) := eval (db n) (ctx := {}) [⟨ "p", ["x"]⟩, ⟨"p", ["y"]⟩]
#eval q_ 10 |>.size
#eval q_ 2 |> toString

def a1 : Atom := ⟨"p", ["x"]⟩
def a2 : Atom := ⟨"q", ["x", "y"]⟩
def a_1 : Atom := ⟨"ev1", ["x"]⟩
def a_2 : Atom := ⟨"ev2", ["x"]⟩
def a_3 : Atom := ⟨"ev3", ["y"]⟩
def a_4 : Atom := ⟨"ev4", ["x"]⟩
def e2 : Query := .effect [] [] [a_2] .nil
def e3 : Query := .effect [] [] [a_3] .nil
def e4 : Query := .effect [] [] [a_4] .nil
def r (name : String) (g : Atom) (a : List Atom) (e : Query) : Rule := (name, [g], .step .all a e)
def r1 : Rule := ("r1", [a_1], .step .all [] $ e2)
def p1 : Program := [r1]
def p2 : Program :=
  [r "1" a_1 [] e2, r "2" a_1 [a1, a2] e3, r "3" a_2 [a_3] e4]

def t1 : Tuple := ⟨"ev1", #[.nat 0]⟩
def d0 : Data := Data.ofTuples [⟨"p", #[0]⟩, ⟨"q", #[0, 1]⟩]
def d1 : Data := Data.ofTuples [⟨"ev1", #[0]⟩]
def s1 : State := .new .seq ⟨d1, #[]⟩
def f1 : Frame := ⟨d1, #[]⟩

def State.adv (n : Nat) (p : Program) : State → State
| s => s.advanceFix p ⟨d0, #[]⟩ n |>.run' 0

#eval let s := s1.adv 40 p2; (s.terminal, s.frame, s.pp)
#eval let s := s1.adv 40 p2; IO.print s.pp

def test1 := let s := s1.adv 30 p2; IO.print s.pp

end Ant

def main : IO Unit := Ant.test1