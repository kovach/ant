import Lean.Parser.Types
import Lean.Parser.Basic
import Lean.Parser.Extension
-- necessary for auto-generation
import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter

open Lean Elab Meta Parser PrettyPrinter

-- todo: match `Lean.Parser.identFnAux` more closely?
def antIdent : Parser := -- {{{
  withAntiquot (mkAntiquot "antIdent" `Foo) {
    fn := fun c s =>
      let startPos := s.pos
      let s := takeWhile1Fn (fun c => c.isAlphanum || "_-?!".contains c) "error??" c s
      mkNodeToken `Foo startPos c s } -- }}}

@[combinator_formatter antIdent] def text.formatter : Formatter := pure ()
@[combinator_parenthesizer antIdent] def text.parenthesizer : Parenthesizer := pure ()