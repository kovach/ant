import Ant.Eval
import Ant.games.ttt

open Ant

def init_test : Rule := [ant_rule| INIT:
  | do +(x y): row x, row y . ]

def turn_test : Rule := [ant_rule| TURN:
  row x | choose: row y; do -(y) +(z): other z . ]

def test : StandardProgram := ([init_test], [turn_test])

def gameLoop (p : StandardProgram) (moveList : List Nat) (stepBound := 100) := do
  let s ← evalThread stepBound moveList p
  IO.println ">>>"
  match s.nextChoice with
  | some vs =>
    IO.println s!"choices: {vs.size}"
    IO.println $ vs.map State.pp
  | _ => pure ()
  IO.println ".."
  IO.println $ reprStr $ s.activeFrame.tuples

#eval gameLoop ttt [0,0,0,0,0,0,0,0/-win-/, 0]