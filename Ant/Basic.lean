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

inductive Value
| nat    (value : Nat)
| entity (id : Id) (cause : List Id) -- todo, fullbindings?
deriving Inhabited, DecidableEq, Repr, BEq, Hashable

instance : ToString Value where
  toString
  | .nat n => toString n
  | .entity id _ => s!"#{toString id}"

instance (n : Nat) : OfNat Value n := ⟨ .entity n [] ⟩

open Std
--abbrev PartialBinding := SmallMap Var (Option Value)
--instance : ToString PartialBinding := ⟨fun l => l.toList |> toString⟩
abbrev        Binding := SmallMap Var Value
instance : ToString Binding := ⟨fun l => l.toList |> toString⟩

--def PartialBinding.toBinding : PartialBinding → Binding := fun c => c.mapVal fun _ v => v.get!

inductive Literal | nat (n : Nat)
inductive Expr | val (val : Literal) | var (var : Var)

instance : Coe String Expr := ⟨.var⟩

structure Atom where
  relation : Relation
  vars : List Expr

--structure Effect where
--  new : List Var
--  free : List Var
--  value : List (List Atom)

inductive SubqueryType | all | chooseOne -- | count (var : Var) -- | chooseAtMost (limit : Var)

inductive Query
| step (type : SubqueryType) (v : List Atom) (cont : Query)
| effect (new : List Var) (free : List Var) (value : List Atom) (cont : Query)
| nil

structure Tuple where
  relation : Relation
  tuple : Array Value
deriving BEq, Hashable

def Relation.toString : Relation → String
| .base s => s
| .subquery r n => toString r ++ s!".{n}"

instance : ToString Relation := ⟨ Relation.toString ⟩

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
| val (.nat n) => .nat n

def Expr.eval? (ctx : Binding) : Expr → Option Value
| var v => ctx.find? v
| val (.nat n) => some $ .nat n

def Atom.subst (config : Binding) (c : Atom) : Tuple :=
  ⟨ c.relation, c.vars.map (Expr.eval config) |>.toArray ⟩

def doNewVars (ctr : Nat) (config : Binding) (new : List Var) : Nat × Binding :=
  let cause := config.toCause
  let config := new.foldr (init := (ctr, config)) fun v (n, config) => (n+1, config.cons v (.entity n cause))
  config

def doNewTuples (config : Binding) (effect : List Atom) : List Tuple := effect.map (Atom.subst config)

def Data.insert : Data → Tuple → Data := fun d t => d.add t.relation t

def Data.ofTuples : List Tuple → Data := fun ts => ts.foldl Data.insert {}

def World.add (w : World) (v : Data) : World := { w with tuples := w.tuples.mergeWith v (f := fun _ v v' => v ++ v') }

-- todo remove?
--def doEffect (ctr : Nat) (config : Binding) (new : List Var) (effect : List Atom) : Nat × List Tuple :=
--  let (n, config) := doNewVars ctr config new
--  (n, effect.map (Atom.subst config))
--def World.effect (w : World) (new : List Var) (effect : List Atom)
--    (config : Binding) : World :=
--  let (n, tuples) := doEffect w.counter config new effect
--  {counter := n, tuples := tuples.foldl (init := w.tuples) Data.insert}
end Effect
end Ant