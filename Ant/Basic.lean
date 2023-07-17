import Ant.Misc

namespace Ant

set_option autoImplicit false

notation "ℕ" => Nat

open Std (AssocList HashMap)

abbrev Var := String
inductive Actor
| player
-- | uniformAtRandom

inductive Relation
| base : String → Relation
| subquery : Relation → Nat → Relation
deriving BEq, Repr, Hashable

def Relation.mk : String → Relation := .base

instance : Coe String Relation := ⟨ .base ⟩

abbrev Id := Nat

inductive Literal | nat (n : Nat) | sym (s : String)
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

instance : ToString Literal where
  toString
  | .nat n => toString n
  | .sym s => "#" ++ s

inductive Value
| val    (value : Literal)
| entity (id : Id) (cause : List Id) -- todo, fullbindings?
deriving Inhabited, DecidableEq, Repr, BEq, Hashable

instance : ToString Value where
  toString
  | .val n => toString n
  | .entity id _ => s!"#{toString id}"

instance (n : Nat) : OfNat Value n := ⟨ .entity n [] ⟩

open Std
abbrev        Binding := SmallMap Var Value
instance : ToString Binding := ⟨fun l => l.toList |> toString⟩

inductive Expr | val (val : Literal) | var (var : Var)

instance : Coe String Expr := ⟨.var⟩

structure Atom where
  relation : Relation
  vars : List Expr

inductive SubqueryType | all | chooseOne -- | count (var : Var) -- | chooseAtMost (limit : Var)

inductive Query
| step (type : SubqueryType) (value : List Atom) (cont : Query)
| effect (new : List Var) (free : List Var) (value : List Atom) (cont : Query)
| subquery (q : Query) (cont : Query)
| count (var : Expr) (value : List Atom) (cont : Query)
| nil

structure Tuple where
  relation : Relation
  tuple : Array Value
deriving BEq, Hashable

instance : ToString Relation where
  toString s :=
  let rec f
  | .base s => s
  | .subquery s n => f s ++ s!".{n}"
  f s

-- todo learn how to write instances for this
instance : ToString Tuple where
  toString := fun ⟨r, vs⟩ => s!"({toString r} {" ".intercalate $ vs.toList.map toString})"

instance : Repr Tuple where
  reprPrec t _ := .text $ toString t

instance : ToString Tuple := ⟨ fun ⟨rel, vs⟩ => s!"({toString rel}, {vs.map toString |>.toList |> " ".intercalate})" ⟩

section HashSet
open Lean
instance (α : Type _) [BEq α] [Hashable α] : Append (Lean.HashSet α) := ⟨ Lean.HashSet.merge ⟩
instance (α : Type _) [BEq α] [Hashable α] : Singleton α (Lean.HashSet α) := ⟨ fun a => HashSet.insert {} a ⟩
instance (α : Type _) [BEq α] [Hashable α] : Insert α (Lean.HashSet α) := ⟨ fun a b => b.insert a ⟩
instance (α : Type _) [BEq α] [Hashable α] [ToString α] : ToString (Lean.HashSet α) := ⟨ fun s => toString $ Lean.HashSet.toList s ⟩
end HashSet

-- todo rename Relation
structure RelationSet where
  tuples : Lean.HashSet Tuple

instance : ToString RelationSet := ⟨ fun ⟨s⟩ => toString s ⟩
instance : Singleton Tuple RelationSet := ⟨ fun t => ⟨{t}⟩ ⟩
instance : Insert Tuple RelationSet := ⟨ fun t ⟨s⟩ => ⟨insert t s⟩ ⟩
instance : ToString RelationSet := ⟨ fun ⟨s⟩ => toString s ⟩
instance : Append RelationSet := ⟨ fun ⟨t1⟩ ⟨t2⟩ => ⟨t1 ++ t2⟩ ⟩

def RelationSet.filter (r : RelationSet) (f : Tuple → Bool) : RelationSet := ⟨ r.tuples.fold (init := {}) fun out t => if f t then out.insert t else out ⟩

abbrev Data := HashMap Relation RelationSet

instance : Append Data := ⟨HashMap.mergeWith (f := fun _ a b => a ++ b)⟩


-- def Data.merge : Data → Data → Data := sorry

structure World where
  tuples : Data
  counter : Nat

structure Frame where
  tuples : Data
  removed : Array Id
deriving Inhabited

instance : ToString Frame := ⟨ fun ⟨ts, rem⟩ => s!"({toString $ ts.toList.map fun (k, v) => (k, v.tuples.size)}, -{toString rem})" ⟩

instance : EmptyCollection Frame := ⟨ {}, {} ⟩

def Tuple.refers (t : Tuple) (id : Id) := t.tuple.any fun | .entity i _ => decide (i = id) | _ => false

-- eagerly remove freed tuples
def Frame.append : Frame → Frame → Frame
| ⟨t₁, f₁⟩, ⟨t₂, f₂⟩ =>
  let t₁' := if f₂.size = 0 then t₁ else t₁.mapVal fun _ v => v.filter fun t => not $ f₂.any fun id => t.refers id
  -- todo: what's happening?
  let f' := f₁ ++ f₂.filter fun v => not $ f₁.contains v
  ⟨t₁' ++ t₂, f'⟩
instance : Append Frame := ⟨Frame.append⟩

section Effect
open Std (AssocList)

def Binding.toCause : Binding → List Id := fun b => b.toList.filterMap fun (_, val) =>
  match val with
  | .entity id _ => some id
  | _ => none

def Expr.eval (ctx : Binding) : Expr → Value
| var v => ctx.find! v
| val lit => .val lit

def Expr.eval? (ctx : Binding) : Expr → Option Value
| var v => ctx.find? v
| val lit => some $ .val lit

def Atom.subst (config : Binding) (c : Atom) : Tuple :=
  ⟨ c.relation, c.vars.map (Expr.eval config) |>.toArray ⟩

def doNewVars (ctr : Nat) (config : Binding) (new : List Var) : Nat × Binding :=
  let cause := config.toCause
  let config := new.foldr (init := (ctr, config)) fun v (n, config) => (n+1, config.cons v (.entity n cause))
  config

abbrev M := StateM (Nat × Array String)
def fresh : M Id := modifyGet fun (s, out) => (s, s+1, out)
def freshStr : M String := do let n ← fresh; pure s!"v{n}"
def trace (msg : String) : M Unit := modifyGet fun (s, out) => ((), s, out.push msg)
def M.run (a : Type _) (m : M a) : IO a := do -- todo, remove IO
  let (out, _, trace) := StateT.run m (0, #[])
  trace.forM IO.println
  pure out

def newVars (config : Binding) (new : List Var) : M Binding :=
  let cause := config.toCause
  new.foldlM (init := config) fun ctx v => do { let e ← fresh; pure $ ctx.cons v (.entity e cause) }

def doNewTuples (config : Binding) (effect : List Atom) : List Tuple := effect.map (Atom.subst config)

def Data.insert : Data → Tuple → Data := fun d t => d.add t.relation t

def Data.ofTuples : List Tuple → Data := fun ts => ts.foldl Data.insert {}

def World.add (w : World) (v : Data) : World := { w with tuples := w.tuples.mergeWith v (f := fun _ v v' => v ++ v') }

end Effect

-- todo: simultaneous
inductive C | seq | chosenSeq | chooseOne

deriving instance Repr for C
deriving instance Repr for Literal
deriving instance Repr for Expr
deriving instance Repr for Atom
deriving instance Repr for SubqueryType
deriving instance Repr for Query
deriving instance Repr for Array
deriving instance Repr for Relation
--deriving instance Repr for Tuple
deriving instance Repr for RelationSet
deriving instance Repr for Frame

end Ant