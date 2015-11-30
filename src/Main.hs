module Main where

import Sudoku

sudokuEx :: [[Maybe Integer]]
sudokuEx = map (map $ \c -> if c == '_' then Nothing else Just ((read [c]) - 1)) [
    "___26_7_1",
    "68__7__9_",
    "19___45__",
    "82_1___4_",
    "__46_29__",
    "_5___3_28",
    "__93___74",
    "_4__5__36",
    "7_3_18___"]

main :: IO ()
main =
    sudoku sudokuEx
