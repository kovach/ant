import Lean
import Ant.Basic
import Lean.Parser.Types
import Ant.Identifier

-- todo: fix number parsing

namespace Ant

open Lean Elab Meta

def freshName : MacroM (TSyntax `term) := do
  let x : TSyntax `ident ← `(x)
  let xname := x.getId.toString
  `($(quote xname))

declare_syntax_cat ant
declare_syntax_cat ant_expr
declare_syntax_cat ant_atom

-- can't use single-quote as the symbol prefix?
syntax antIdent : ant_expr
syntax "#" noWs antIdent : ant_expr
syntax num : ant_expr
syntax antIdent ant_expr* : ant_atom
syntax "[ant|" ant "]" : term
syntax "[ant|" ant_atom,* "]" : term
syntax "[ant_expr|" ant_expr "]" : term
syntax "[ant_atom|" ant_atom "]" : term

def str : TSyntax `Foo → MacroM (TSyntax `term) := fun x => `($(quote x.raw[0].getAtomVal))

def Expr.parse.sym : TSyntax `Foo → MacroM (TSyntax `term) := fun x =>
  `(Expr.val $ Literal.sym $(quote $ x.raw[0].getAtomVal))

def Expr.parse.var : TSyntax `Foo → MacroM (TSyntax `term) := fun x =>
  match x.raw[0].getAtomVal.toList with
  | ['_'] => freshName -- "hole" variables marked by `_` are unconstrained
  | n => `(Expr.var $(quote $ n.asString))

#check Expr.parse.var
macro_rules
| `([ant_expr| $n:num]) => `(Expr.val (Literal.nat $n))
| `([ant_expr| $n:antIdent]) => do `($(← Expr.parse.var n)) --  `(Expr.var $(← str n))
| `([ant_expr| #$n:antIdent]) => do `($(← Expr.parse.sym n)) --  `(Expr.var $(← str n))

| `([ant| $atoms:ant_atom,*]) => do
  let vs ← atoms.getElems.mapM fun e => `([ant_atom| $e])
  `([$vs,*])

| `([ant_atom| $n:antIdent $vs:ant_expr*]) => do
  let vs ← vs.mapM fun e => `([ant_expr| $e])
  `(Atom.mk (Relation.base $(← str n)) [$vs,*])

#check [ant| first a b, ok-then?! b #foo 3]

/- e.g.
want-activate ev p c | in-play c; choose: player-action-target-from? p c target source; do: activate ev c, target ev l.
activate ev c | flash-flood c, target ev l; do: dmg ev l 1; coastal l; do dmg ev l 1.
-/

declare_syntax_cat ant_clause
declare_syntax_cat ant_body

syntax "count" ant_expr ":" ant_atom,* : ant_clause
syntax ant_atom,* : ant_clause
syntax "choose:" ant_atom,* : ant_clause
syntax "do:" ant_atom,* : ant_clause
syntax "do" ("-(" antIdent,* ")")? ("+(" antIdent,* ")")? ":" ant_atom,* : ant_clause
syntax ant_clause : ant_body
syntax ant_clause ";" ant_body : ant_body
syntax "(" ant_body ")" : ant_clause
syntax "[ant_clause|" ant_clause "]" : term
syntax "[ant_body|" ant_body "]" : term
syntax "[ant_atoms|" ant_atom,* "]" : term

macro_rules
-- helper
| `([ant_atoms| $atoms:ant_atom,*]) => do
    let atoms ← atoms.getElems.mapM fun e => `([ant_atom| $e])
    `([$atoms,*])

| `([ant_clause| $atoms:ant_atom,*]) => do
    `(fun k => Query.step .all [ant_atoms| $atoms,*] k)
| `([ant_clause| choose: $atoms:ant_atom,*]) => do
    `(fun k => Query.step .chooseOne [ant_atoms| $atoms,*] k)
| `([ant_clause| do: $atoms:ant_atom,*]) => do
    `(fun k => Query.effect [] [] [ant_atoms| $atoms,*] k)

| `([ant_clause| count $n : $atoms:ant_atom,*]) => do
    `(fun k => Query.count [ant_expr| $n] [ant_atoms| $atoms,*] k)

| `([ant_clause| ( $q:ant_body )]) => `(fun k => Query.subquery [ant_body| $q] k)

-- do-type clause has optional list of *destroyed* (free) entities and *created* (new) entities
| `([ant_clause| do $[-($free:antIdent,*)]? $[+( $new:antIdent,* )]? : $atoms:ant_atom,*]) => do
    let new  ← match new with | none => pure #[] | some v => v.getElems.mapM str
    let free  ← match free with | none => pure #[] | some v => v.getElems.mapM str
    `(fun k => Query.effect [$new,*] [$free,*] [ant_atoms| $atoms,*] k)

| `([ant_body| $c:ant_clause]) => `([ant_clause| $c] .nil)
| `([ant_body| $c:ant_clause ; $k:ant_body]) =>
    `([ant_clause| $c] [ant_body| $k])

#check Option.getD
#reduce [ant_body| p1 a b, p2 b c]
#reduce [ant_body| p1 a b, p2 b c; p1 b]
#reduce [ant_body| p1 a b; choose: p2 b c]
#reduce [ant_body| p1 a b; choose: p2 b c; do: p3]
#reduce [ant_body| p1 a b; choose: p2 b c; do +(x): p3 x]
#reduce [ant_body| p1 a b; choose: p2 b c; do -(x, y) +(z): p 3 z 4]
#reduce [ant_body| p x; count n: q x y ]
#reduce [ant_body| p x; count 3 : q x y ]
#reduce [ant_body| p x; ( q x y; do: out y )]

declare_syntax_cat ant_rule

syntax antIdent ":" ant_atom,* "|" ant_body "." : ant_rule
syntax "[ant_rule|" ant_rule "]" : term

macro_rules
| `([ant_rule| $n:antIdent : $guard:ant_atom,* | $body:ant_body .]) => do
    `(($(← str n), [ant_atoms| $guard,*], [ant_body| $body]))

#reduce [ant_rule| name: ev _ _ | p1 a b; choose: p c b 3 5, p b c; do +(x): p' 3 x 4 .]

end Ant