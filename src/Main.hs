module Main where

import Sudoku
import Battleship

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

battleshipEx :: BattleshipInst
battleshipEx =
    let grid = map (map battleShipCharToInput) [
            "        ~ ",
            "          ",
            "          ",
            "   o      ",
            "          ",
            "          ",
            "    ^     ",
            "          ",
            "          ",
            "          "]
        shipNums = [4, 3, 2, 1]
        rowCounts = [4, 0, 0, 1, 2, 4, 2, 3, 0, 4]
        colCounts = [4, 1, 0, 1, 2, 1, 4, 2, 5, 0]
    in (shipNums, grid, rowCounts, colCounts)

battleShipCharToInput :: Char -> BattleshipInput
battleShipCharToInput ' ' = NoInfo
battleShipCharToInput '~' = Wavy
battleShipCharToInput 'o' = Circle
battleShipCharToInput 'S' = Square
battleShipCharToInput '<' = FaceRight
battleShipCharToInput '>' = FaceLeft
battleShipCharToInput 'v' = FaceUp
battleShipCharToInput '^' = FaceDown
battleShipCharToInput _ = error "Invalid battleship char"

main :: IO ()
main = do
    sudoku sudokuEx
    battleship battleshipEx
