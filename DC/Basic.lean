import Std.Data.AssocList
import Std.Data.HashMap
abbrev Map (k v : Type _) := Std.AssocList k  v

open Std (AssocList HashMap)

def Map.lookup [BEq k] (m : Map k v) (key : k) : Option v := AssocList.find? key m
def Map.lookup! [BEq k] [Inhabited v] (m : Map k v) (key : k) : v :=
  match AssocList.find? key m with
  | some v => v
  | none => default

def List.eraseDupStable_aux [DecidableEq α] (seen : List α) : List α → List α
| [] => []
| x :: xs => if x ∈ seen then eraseDupStable_aux seen xs else x :: (eraseDupStable_aux (x :: seen) xs)

def List.eraseDupStable [DecidableEq α] : List α → List α := eraseDupStable_aux []

abbrev Var := String
abbrev Actor := String
abbrev Relation := String

inductive QuantifierType
| all
| create
| le (limit : Nat) (actor : Actor)
| eq (limit : Nat) (actor : Actor)
deriving Repr

structure ChoiceNode

structure Clause where
  relation : Relation
  vars : List Var
deriving Repr

abbrev QuantifiedVar := Var × QuantifierType
structure Query where
  ordering : List QuantifiedVar
  clauses : List Clause
deriving Repr

structure Effect where
  query : Query
  result : List Clause

inductive Value
| entity (value : Nat)
| nat (value : Nat)
deriving Inhabited, DecidableEq, Repr

structure Tuple where
  relation : Relation
  tuple : Array Value

abbrev Data := HashMap Relation (Array Tuple)

structure World where
  tuples : Data
  counter : Nat

abbrev Configuration := Map Var (Option Value)
abbrev DefiniteConfiguration := Map Var Value

def defaultQueryVars : List Clause → List Var :=
  fun cs => (cs.map fun c => c.vars) |>.join |>.eraseDupStable
def Query.ofList : List Clause → Query := fun cs =>
  { ordering := (defaultQueryVars cs).map fun v => (v, .all), clauses := cs }