import Std.Data.AssocList
import Std.Data.HashMap
import Std.Data.RBMap
import Std.Lean.HashSet

open Std (AssocList HashMap)

instance [Repr a] [Repr b] : Repr (AssocList a b) := ⟨fun l n => reprPrec l.toList n⟩
instance [BEq a] [Hashable a] [Repr a] [Repr b] : Repr (HashMap a b) := ⟨(reprPrec ·.toList)⟩
instance [BEq a] [Hashable a] [Repr a] : Repr (Lean.HashSet a) := ⟨(reprPrec ·.toList)⟩

namespace Array

def splitAt (n : Nat) (as : Array α) : Array α × Array α :=
  Prod.snd $ as.foldl (init := (n, #[], #[])) fun (n, as, bs) a =>
    match n with
    | 0 => (n, as, bs.push a)
    | n+1 => (n, as.push a, bs)

def splitAt' (n : Nat) (as : Array α) : Array α × Option α × Array α :=
  Prod.snd $ as.foldl (init := (n, #[], none, #[])) fun (n, as, val, bs) a =>
    match n, val with
    | 0, none => (n, as, some a, bs)
    | 0, _ => (n, as, val, bs.push a)
    | n+1, _ => (n, as.push a, val, bs)

end Array

namespace List
def toHashSet (l : List a) [BEq a] [Hashable a] : Lean.HashSet a := l.foldl Lean.HashSet.insert {}
end List

namespace Std
abbrev SmallMap (k v : Type _) := AssocList k  v

def AssocList.find! [BEq k] [Inhabited v] (m : SmallMap k v) (key : k) : v :=
  match AssocList.find? key m with
  | some v => v
  | none => default

--def HashMap.add [BEq k] [Hashable k] (self : HashMap k (List v)) (key : k) (value : v) : HashMap k (List v) :=
--  self.modify key fun _ values => value :: values
--
--def HashMap.add [BEq k] [Hashable k] (self : HashMap k (List v)) (key : k) (value : v) : HashMap k (List v) :=
--  self.modify key fun _ values => value :: values

def HashMap.add [BEq k] [Hashable k] [Singleton v t] [Insert v t] (self : HashMap k t) (key : k) (value : v) : HashMap k t :=
  if self.contains key
  then self.modify key fun _ values => Insert.insert value values
  else self.insert key {value}
end Std

def List.eraseDupStable_aux [DecidableEq α] (seen : List α) : List α → List α
| [] => []
| x :: xs => if x ∈ seen then eraseDupStable_aux seen xs else x :: (eraseDupStable_aux (x :: seen) xs)

def List.eraseDupStable [DecidableEq α] : List α → List α := eraseDupStable_aux []

@[always_inline, inline]
protected def StateT.modify [Monad m] (f : σ → σ) : StateT σ m Unit :=
  fun s => pure ((), f s)