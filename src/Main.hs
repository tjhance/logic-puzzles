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

battleshipEx1 :: BattleshipInst
battleshipEx1 =
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

battleshipEx2 :: BattleshipInst
battleshipEx2 =
    let grid = map (map battleShipCharToInput) [
            "          ",
            "         v",
            "          ",
            "   ~      ",
            "          ",
            "          ",
            "       S  ",
            "         ^",
            "          ",
            "          "]
        shipNums = [4, 3, 2, 1]
        rowCounts = [3, 1, 1, 3, 2, 2, 1, 2, 4, 1]
        colCounts = [1, 4, 0, 3, 2, 2, 0, 3, 1, 4]
    in (shipNums, grid, rowCounts, colCounts)

battleshipEx3 :: BattleshipInst
battleshipEx3 =
    let grid = map (map battleShipCharToInput) [
            "          ",
            "        o ",
            "    ~     ",
            "          ",
            "~         ",
            "          ",
            "  o       ",
            "          ",
            "          ",
            "          "]
        shipNums = [4, 3, 2, 1]
        rowCounts = [0, 1, 3, 3, 4, 3, 4, 0, 1, 1]
        colCounts = [4, 0, 4, 2, 2, 0, 4, 0, 4, 0]
    in (shipNums, grid, rowCounts, colCounts)

battleshipEx4 :: BattleshipInst
battleshipEx4 =
    let grid = map (map battleShipCharToInput) [
            "          ",
            "o         ",
            "          ",
            "  ~       ",
            "          ",
            "          ",
            "          ",
            "      S   ",
            "          ",
            "          "]
        shipNums = [4, 3, 2, 1]
        rowCounts = [1, 1, 0, 2, 6, 2, 1, 1, 6, 0]
        colCounts = [4, 1, 4, 1, 2, 1, 3, 1, 1, 2]
    in (shipNums, grid, rowCounts, colCounts)

battleshipEx5 :: BattleshipInst
battleshipEx5 =
    let grid = map (map battleShipCharToInput) [
            "o         ",
            "          ",
            "     S    ",
            "          ",
            "<         ",
            "          ",
            "          ",
            "          ",
            "          ",
            "          "]
        shipNums = [4, 3, 2, 1]
        rowCounts = [1, 2, 1, 1, 2, 0, 5, 2, 4, 2]
        colCounts = [3, 3, 1, 2, 0, 4, 2, 3, 2, 0]
    in (shipNums, grid, rowCounts, colCounts)

battleshipEx6 :: BattleshipInst
battleshipEx6 =
    let grid = map (map battleShipCharToInput) [
            "          ",
            "          ",
            "          ",
            "          ",
            "o         ",
            "          ",
            "         ~",
            "          ",
            "          ",
            "          "]
        shipNums = [4, 3, 2, 1]
        rowCounts = [0, 2, 0, 0, 3, 3, 5, 2, 5, 0]
        colCounts = [1, 2, 2, 3, 0, 3, 1, 4, 0, 4]
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
    battleship battleshipEx1
    battleship battleshipEx2
    battleship battleshipEx3
    battleship battleshipEx4
    battleship battleshipEx5
    battleship battleshipEx6
