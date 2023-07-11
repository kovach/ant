import Lean
import Ant.Basic
import Lean.Parser.Types
import Ant.Identifier

namespace Ant

open Lean Elab Meta

declare_syntax_cat ant
declare_syntax_cat ant_expr
declare_syntax_cat ant_atom

syntax antIdent : ant_expr
syntax antIdent ant_expr* : ant_atom
syntax "[ant|" ant "]" : term
syntax "[ant|" ant_atom,* "]" : term
syntax "[ant_expr|" ant_expr "]" : term
syntax "[ant_atom|" ant_atom "]" : term

def str : TSyntax `Foo → String := fun x => x.raw[0].getAtomVal

macro_rules
| `([ant_expr| $n:antIdent]) => `($(quote $ str n))

| `([ant| $atoms:ant_atom,*]) => do
  let vs ← atoms.getElems.mapM fun e => `([ant_atom| $e])
  `([$vs,*])

| `([ant_atom| $n:antIdent $vs:ant_expr*]) => do
  let rel ← `($(quote $ str n))
  let vs ← vs.mapM fun e => `([ant_expr| $e])
  `(Atom.mk (Relation.base $rel) [$vs,*])

#check [ant| first a b, ok-then?! b c]

/- e.g.
want-activate ev p c | in-play c; choose: player-action-target-from? p c target source; do: activate ev c, target ev l.
activate ev c | flash-flood c, target ev l; do: dmg ev l 1; coastal l; do dmg ev l 1.
-/

declare_syntax_cat ant_clause
declare_syntax_cat ant_body

syntax ant_atom,* : ant_clause
syntax "choose:" ant_atom,* : ant_clause
syntax "do:" ant_atom,* : ant_clause
syntax "do" antIdent* ":" ant_atom,* : ant_clause
syntax ant_clause : ant_body
syntax ant_clause ";" ant_body : ant_body
syntax "[ant_clause|" ant_clause "]" : term
syntax "[ant_body|" ant_body "]" : term
syntax "[ant_atoms|" ant_atom,* "]" : term

-- todo reduce duplication below
-- def Query.syntax.part : MacroM Syntax

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
| `([ant_clause| do $vs:antIdent* : $atoms:ant_atom,*]) => do
    let vs ← vs.mapM fun e => `($(quote $ str e))
    `(fun k => Query.effect [$vs,*] [] [ant_atoms| $atoms,*] k)

| `([ant_body| $c:ant_clause]) => `([ant_clause| $c] .nil)
| `([ant_body| $c:ant_clause ; $k:ant_body]) =>
    `([ant_clause| $c] [ant_body| $k])

#reduce [ant_body| p1 a b, p2 b c]
#reduce [ant_body| p1 a b, p2 b c; p1 b]
#reduce [ant_body| p1 a b; choose: p2 b c]
#reduce [ant_body| p1 a b; choose: p2 b c; do: p3]
#reduce [ant_body| p1 a b; choose: p2 b c; do x: p3 x]

declare_syntax_cat ant_rule

syntax antIdent ":" ant_atom,* "|" ant_body "." : ant_rule
syntax "[ant_rule|" ant_rule "]" : term

macro_rules
| `([ant_rule| $n:antIdent : $guard:ant_atom,* | $body:ant_body .]) => do
    `(($(quote $ str n), [ant_atoms| $guard,*], [ant_body| $body]))

#reduce [ant_rule| name: ev e | p1 a b; choose: p2 c b, p2 b c; do x: p3 x.]

end Ant