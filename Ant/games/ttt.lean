import Ant.Parser
import Main

namespace Ant

def ttt_init_grid : Rule := [ant_rule| game-loop:
  start |
    do: row 1, row 2, row 3, col 1, col 2, col 3;
    row r, col c;
    do +(t): empty t r c.
]

def ttt_init_players : Rule := [ant_rule| game-loop:
  start |
    do +(now): opponent 1 2, opponent 2 1, turn now 1.
]

def ttt_turn : Rule := [ant_rule| game-loop:
  turn now m | choose: empty e r c; opponent m m';
  do -(now e) +(next): mark r c m, turn next m'.
]

def ttt_win_conditions : List Rule := [
  [ant_rule| win_row:    mark _ _ _ | mark r 1 m, mark r 2 m, mark r 3 m; do: win m.],
  [ant_rule| win_col:    mark _ _ _ | mark 1 c m, mark 2 c m, mark 3 c m; do: win m.],
  [ant_rule| win_diag_1: mark _ _ _ | mark 1 1 m, mark 2 2 m, mark 3 3 m; do: win m.],
  [ant_rule| win_diag_2: mark _ _ _ | mark 1 3 m, mark 2 2 m, mark 3 1 m; do: win m.]
]

end Ant