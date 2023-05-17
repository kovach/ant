abbrev Var := String
abbrev Actor := String
abbrev Relation := String

inductive QuantifierType
| all
| new
| le (limit : ℕ) (actor : Actor)
| eq (limit : ℕ) (actor : Actor)

structure ChoiceNode

structure Clause where
  relation : Relation
  vars : List Var

structure Query where
  ordering : List (Var × Quantifier)
  clauses : List Clause

inductive Value
| entity (value : Nat)
| nat (value : Nat)
deriving Inhabited, DecidableEq, Repr

abbrev Tuple := Array Value

abbrev Map (k v : Type _) := List (k × v)
def Map.lookup [DecidableEq k] (m : Map k v) (key : k) : Option v :=
  match m with
  | [] => none
  | (k', val) :: m' => if key = k' then some val else lookup m' key


def Data := Map Relation (List Tuple)
def Configuration := Map Var (Option Value)



structure Effect where
  query : Query
  result : List Clause