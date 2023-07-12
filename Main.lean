import Ant.Eval
import Ant.games.ttt

open Ant

#eval evalThread [] ttt |>.nextChoice |> Option.map (Array.map State.pp)