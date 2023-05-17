import DC.Basic
import Lean

open Lean Elab Meta

declare_syntax_cat dc_rel
declare_syntax_cat dc_var
declare_syntax_cat dc_clause
declare_syntax_cat dc_query
syntax ident : dc_rel
syntax ident : dc_var
syntax dc_rel dc_var* : dc_clause
syntax dc_clause,* : dc_query

partial def elabRel : Syntax → MetaM Expr
| `(dc_rel| $r:ident) => pure $ mkStrLit r.getId.toString
| _ => throwUnsupportedSyntax

partial def elabVar : Syntax → MetaM Expr
| `(dc_var| $r:ident) => pure $ mkStrLit r.getId.toString
| _ => throwUnsupportedSyntax

partial def elabClause : Syntax → MetaM Expr
| `(dc_clause| $r:dc_rel $vars:dc_var*) => do
  let vars ← List.mapM vars.toList (f := fun v => elabVar v.raw)
  mkAppM ``Clause.mk #[(← elabRel r), (← mkListLit (.const ``String []) vars)]
| _ => throwUnsupportedSyntax

partial def elabQuery : Syntax → MetaM Expr
| `(dc_query| $c:dc_clause,*) => do
  let c ← c.getElems.mapM fun c => elabClause c
  mkListLit (.const ``Clause []) c.toList
| _ => throwUnsupportedSyntax


elab ">>r" p:dc_rel "<<" : term => elabRel p
elab ">>v" p:dc_var "<<" : term => elabVar p
elab ">>c" p:dc_clause "<<" : term => elabClause p
elab ">>" p:dc_query "<<" : term => elabQuery p

#check >>r rel <<
#check >>v x <<
#check >>c x y xz <<
#check >> x y xz, p x <<