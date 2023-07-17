import Ant.Eval
import Ant.games.ttt
import Socket

open Ant

def init_test : Rule := [ant_rule| INIT:
  | do: make 2, make 33, make 1, make 2;
    (make n; do: succ n);
    count n: succ _;
    do: total n .]

def turn_test : Rule := [ant_rule| TURN:
  make n | . ]

def test : StandardProgram := Program.parse [init_test, turn_test]

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

def main : IO Unit := pure ()

--#eval gameLoop ttt [0,0,0,0,0,0,0,0/-win-/, 0]
#eval gameLoop test []