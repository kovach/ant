import DC.Basic2
import Lean

namespace DC

open Lean Elab Meta

declare_syntax_cat dc_rel
declare_syntax_cat dc_var
declare_syntax_cat dc_var_binding
declare_syntax_cat dc_clause -- rename this atom
declare_syntax_cat dc_query
syntax ident : dc_rel
syntax ident : dc_var
syntax ident : dc_var_binding
syntax "!" ident : dc_var_binding
syntax dc_rel dc_var* : dc_clause
syntax dc_clause,* : dc_query
syntax "[" dc_var_binding* "]" dc_clause,* : dc_query

partial def elabRel : Syntax → MetaM Expr
| `(dc_rel| $r:ident) => pure $ mkStrLit r.getId.toString
| _ => throwUnsupportedSyntax

partial def elabVar : Syntax → MetaM Expr
| `(dc_var| $r:ident) => pure $ mkStrLit r.getId.toString
| _ => throwUnsupportedSyntax

--partial def elabVarBinding : Syntax → MetaM Expr
----| `(dc_var_binding| $r:ident) => mkAppM ``Prod.mk #[mkStrLit r.getId.toString, .const ``QuantifierType.all []]
--| `(dc_var_binding| ! $r:ident) => do
--    let quant ← mkAppM ``QuantifierType.eq #[mkNatLit 1, mkStrLit "player"]
--    mkAppM ``Prod.mk #[mkStrLit r.getId.toString, quant]
--| _ => throwUnsupportedSyntax

partial def elabClause : Syntax → MetaM Expr
| `(dc_clause| $r:dc_rel $vars:dc_var*) => do
  let vars ← List.mapM vars.toList (f := fun v => elabVar v.raw)
  mkAppM ``Atom.mk #[(← elabRel r), (← mkListLit (.const ``String []) vars)]
| _ => throwUnsupportedSyntax

partial def elabQuery : Syntax → MetaM Expr
| `(dc_query| $c:dc_clause,*) => do
  let c ← c.getElems.mapM fun c => elabClause c
  let clauses ← mkListLit (.const ``Atom []) c.toList
  mkAppM ``Query.ofList #[clauses]
--| `(dc_query| [ $v* ] $c:dc_clause,*) => do
--  let v ← v.mapM elabVarBinding
--  let c ← c.getElems.mapM elabClause
--  mkAppM ``Query.mk #[(← mkListLit (.const ``QuantifiedVar []) v.toList), (← mkListLit (.const ``Atom []) c.toList)]
--  --let vars := defaultQueryVars c
| _ => throwUnsupportedSyntax


elab ">>r" p:dc_rel "<<" : term => elabRel p
elab ">>v" p:dc_var "<<" : term => elabVar p
elab ">>c" p:dc_clause "<<" : term => elabClause p
elab ">>"  p:dc_query "<<" : term => elabQuery p

#check >>r rel <<
#check >>v x <<
#check >>c x y xz <<
#eval >> p y z, q x <<
#eval >>
  [x !y z] p y z, q x
<<
#eval >> [land !token] token_located token land <<

end DC