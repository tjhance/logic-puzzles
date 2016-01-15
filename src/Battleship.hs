{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}

module Battleship where

import Control.Applicative
import Control.Monad
import Data.Attoparsec.ByteString (Parser)
import Data.Attoparsec.ByteString.Char8
import Data.Char (ord)
import Data.SBV
import Data.Generics
import Data.List (transpose)
import Data.Map (Map, (!))
import Data.Traversable (forM)
import Control.Monad (forM_)

import Util

{-- Description of an instance of a Battleship Puzzle
    - Number of each size of ship (e.g. [4, 3, 2, 1] in most games,
      that is, 4 subs, 3 destryers, 2 cruisers, 1 battleship)
    - Input grid. All the types of cells you can see in an input grid.
    - The counts for each row.
    - The counts for each column.
 --}
type BattleshipInst = ([Integer], [[BattleshipInput]], [Integer], [Integer])
data BattleshipInput = Circle
                     | Square
                     | FaceLeft
                     | FaceRight
                     | FaceUp
                     | FaceDown
                     | Wavy
                     | NoInfo
    deriving (Eq, Show, Ord)

{-- Model of the space of Battleship solutions
    Each cell has a CellType: either empty, part of a horizontal ship, or part
    of a vertical ship. (By convention, singleton ships will be horizontal.)
    The two numbers will be an index `i` and size `n`.
    `n` is the size of the ship and `i` is the index in it, 0 <= i < n.
    0 is the topmost or leftmost ship and n-1 is the bottommost or rightmost.
 --}
data CellType = Empty | Horiz | Vert deriving (Show, Read, Eq, Ord, Data, SymWord, HasKind)
type CellState = (SBV CellType, SWord8, SWord8)

-- Constraints that go on every cell. A ship is either empty, horizontal, or vertical.
-- For empty cells, by convention we set i=0, n=0
-- Singletons are horizontal by convention, so a vertical ship must have n>=2
-- Of course, 0 <= i < n for non-empty cells.
baseCellConstraint :: Word8 -> CellState -> SBool
baseCellConstraint maxShipSize (ctype, i, n) =
    (ctype .== literal Empty &&& i .== literal 0 &&& n .== literal 0) |||
    (ctype .== literal Horiz &&& literal 0 .<= i &&& i .< n &&& literal 1 .<= n &&& n .<= literal maxShipSize) |||
    (ctype .== literal Vert &&& literal 0 .<= i &&& i .< n &&& literal 2 .<= n &&& n .<= literal maxShipSize)

-- Constraint on what the cell can be given its input.
isCellStateOkay :: BattleshipInput -> CellState -> SBool
isCellStateOkay NoInfo (ctype, i, n) = literal true
-- wavy symbol: cell is empty
isCellStateOkay Wavy (ctype, i, n) = (ctype .== literal Empty)
-- circle symbol: cell is singleton
isCellStateOkay Circle (ctype, i, n) = (ctype .== literal Horiz &&& i .== literal 0 &&& n .== literal 1)
-- square symbol: ship could be horizontal or vertical, and this cell is not on either end
isCellStateOkay Square (ctype, i, n) = (ctype ./= literal Empty &&& n .>= 2 &&& i ./= 0 &&& i ./= (n - 1))
-- ship points to the right: cell is first on a horizontal ship
isCellStateOkay FaceRight (ctype, i, n) = (ctype .== literal Horiz &&& i .== literal 0 &&& n .>= literal 2)
-- ship points to the left: cell is last on a horizontal ship
isCellStateOkay FaceLeft (ctype, i, n) = (ctype .== literal Horiz &&& i .== (n - literal 1) &&& n .>= literal 2)
-- ship points down: cell is first on a vertical ship
isCellStateOkay FaceDown (ctype, i, n) = (ctype .== literal Vert &&& i .== 0 &&& n .>= literal 2)
-- ship points up: cell is last on a vertical ship
isCellStateOkay FaceUp (ctype, i, n) = (ctype .== literal Vert &&& i .== (n - literal 1) &&& n .>= literal 2)

{-- "Global" constraints based on sums
    Here we count both that the total number of ships of each length is correct
    and that the counts in each row or column are correct.
    To count the number of ships, we count the number of cells with i=0 and n=shipSize
 --}

-- First argument is a row (or column)
-- Second argument is the number of non-empty cells we expect in that row
numNonemptyInRow :: [CellState] -> Word8 -> SBool
numNonemptyInRow cells target =
    (sum (map (\cell ->
        ite (nonempty cell)
            (literal 1)
            (literal 0)
    ) cells)) .== literal target
  where
    nonempty :: CellState -> SBool
    nonempty (ctype, i, n) = ctype ./= literal Empty

-- First argument is the grid
-- Second argument is the number of the size of the ship to count
-- Third argument is how many of that ship we expect to find.
numOfShipsIs :: [[CellState]] -> Word8 -> Word8 -> SBool
numOfShipsIs cells shipSize numShips =
    (sum (map (\(ctype, i, n) ->
        ite (i .== literal 0 &&& n .== literal shipSize)
            (literal 1)
            (literal 0)
    ) (concat cells))) .== literal numShips

{-- "Local" constraints connecting cells that are part of the same ship and
    the fact that ships cannot be adjacent. --}

constrainHorizontallyAdj :: CellState -> CellState -> SBool
constrainHorizontallyAdj = constrainAdj Horiz Vert

constrainVerticallyAdj :: CellState -> CellState -> SBool
constrainVerticallyAdj = constrainAdj Vert Horiz

constrainLeftCell :: CellState -> SBool
constrainLeftCell = constrainFirst Horiz Vert

constrainTopCell :: CellState -> SBool
constrainTopCell = constrainFirst Vert Horiz

constrainRightCell :: CellState -> SBool
constrainRightCell = constrainLast Horiz Vert

constrainBotCell :: CellState -> SBool
constrainBotCell = constrainLast Vert Horiz

-- Each of these takes two arguments horiz and vert
-- So, e.g., the implementation of constrainAdj lets you imagine
-- horizontally adjacent cells but you can flip the arguments and pass
-- in horiz=Vert, vert=Horiz and it will work for vertically adjacent cells too.

-- For two horizontally adjacent cells, if one is of a vertical ship, the other must
-- be empty. Furthermore, if one of them is of a horizontal ship, then either
-- the second one must be horizontal and the first of its ship, and the first empty,
-- or the first must be horizontal and the last of ships, and the second empty,
-- or they are both horizontal and adjacent within their ship.
constrainAdj :: CellType -> CellType -> CellState -> CellState -> SBool
constrainAdj horiz vert (ctype1, i1, n1) (ctype2, i2, n2) =
    (ctype1 .== literal Empty &&& (
        ctype2 .== literal Empty ||| ctype2 .== literal vert |||
        (ctype2 .== literal horiz &&& i2 .== literal 0)
    )) |||
    (ctype1 .== literal vert &&& (
        ctype2 .== literal Empty
    )) |||
    (ctype1 .== literal horiz &&& (
        (ctype2 .== literal Empty &&& i1 + 1 .== n1) |||
        (ctype2 .== literal horiz &&& i1 + 1 .== i2 &&& n1 .== n2)
    ))

-- For the leftmost cell in a row, it must either be empty, vertical,
-- or the first in its horizontal ship.
constrainFirst :: CellType -> CellType -> CellState -> SBool
constrainFirst horiz vert (ctype, i, n) =
    (ctype .== literal Empty) ||| (ctype .== literal vert) |||
    (ctype .== literal horiz &&& i .== literal 0)

-- For the rightmost cell in a row, it must either be empty, vertical,
-- or the last in its horizontal ship.
constrainLast :: CellType -> CellType -> CellState -> SBool
constrainLast horiz vert (ctype, i, n) =
    (ctype .== literal Empty) ||| (ctype .== literal vert) |||
    (ctype .== literal horiz &&& i .== n - literal 1)

-- For any two diagonally adjacent cells, at least one must be empty.
constrainDiagonallyAdj :: CellState -> CellState -> SBool
constrainDiagonallyAdj (ctype1, i1, n1) (ctype2, i2, n2) =
    ctype1 .== literal Empty |||
    ctype2 .== literal Empty

-- Some utility functions for manipulating a 2d grid

allHorizPairs :: [[a]] -> [(a, a)]
allHorizPairs grid = concat $ map pairsInRow grid
    where pairsInRow (x:y:rest) = (x, y) : pairsInRow (y:rest)
          pairsInRow [x] = []
          pairsInRow [] = []

allVertPairs :: [[a]] -> [(a, a)]
allVertPairs = allHorizPairs . transpose

allDiagPairs :: [[a]] -> [(a, a)]
allDiagPairs grid =
    let height = length grid
        width = length (grid !! 0)
        cell i j = (grid !! i) !! j
    in
        concat $ map (\i ->
            concat $ map (\j ->
                (if j > 0 then [(cell i j, cell (i+1) (j-1))] else []) ++
                (if j < width-1 then [(cell i j, cell (i+1) (j+1))] else [])
            ) [0 .. width-1]
        ) [0 .. height-2]

allTop :: [[a]] -> [a]
allTop grid = grid !! 0

allLeft :: [[a]] -> [a]
allLeft grid = map (!! 0) grid

allBot :: [[a]] -> [a]
allBot grid = grid !! (length grid - 1)

allRight :: [[a]] -> [a]
allRight grid = let width = length (grid !! 0)
                in map (!! (width - 1)) grid

{- Put all the constrains together for a given input puzzle. -}
predicate :: BattleshipInst -> Symbolic SBool
predicate inst = do
    let (instShipTypes, instCells, rowCounts, colCounts) = inst
    let height = length instCells
    let width = length (instCells !! 0)
    let maxShipSize = length instShipTypes + 1

    board <-
        forM [0 .. height-1] $ \r ->
            forM [0 .. width-1] $ \c -> do
                ctype <- symbolic ("ctype-" ++ show r ++ "-" ++ show c)
                i <- symbolic ("i-" ++ show r ++ "-" ++ show c)
                n <- symbolic ("n-" ++ show r ++ "-" ++ show c)
                return ((ctype, i, n) :: CellState)

    addConstraints $ do
        forM_ (zip instCells board) $ \(instRow, boardRow) ->
            forM_ (zip instRow boardRow) $ \(input, cell) -> do
                addConstraint $ baseCellConstraint (fromIntegral maxShipSize) cell
                addConstraint $ isCellStateOkay input cell

        forM_ (allHorizPairs board) $ \(a, b) -> addConstraint $ constrainHorizontallyAdj a b
        forM_ (allVertPairs board) $ \(a, b) -> addConstraint $ constrainVerticallyAdj a b
        forM_ (allDiagPairs board) $ \(a, b) -> addConstraint $ constrainDiagonallyAdj a b
        forM_ (allLeft board) $ \a -> addConstraint $ constrainLeftCell a
        forM_ (allTop board) $ \a -> addConstraint $ constrainTopCell a
        forM_ (allRight board) $ \a -> addConstraint $ constrainRightCell a
        forM_ (allBot board) $ \a -> addConstraint $ constrainBotCell a

        forM_ (zip rowCounts board) $ \(rowCount, row) ->
            addConstraint $ numNonemptyInRow row (fromIntegral rowCount)
        forM_ (zip colCounts (transpose board)) $ \(colCount, col) ->
            addConstraint $ numNonemptyInRow col (fromIntegral colCount)

        forM_ (zip [1..] instShipTypes) $ \(shipSize, numShips) ->
            addConstraint $ numOfShipsIs board (fromIntegral shipSize) (fromIntegral numShips)

-- Returns a string representation of the result
getSolution :: BattleshipInst -> Map String CW -> String
getSolution inst m = 
    let (instShipTypes, instCells, rowCounts, colCounts) = inst
        height = length instCells
        width = length (instCells !! 0)
    in
        concat $ map (\r ->
            (concat $ map (\c ->
                let ctype = fromCW (m ! ("ctype-" ++ show r ++ "-" ++ show c)) :: CellType
                in if ctype == Empty then "." else "O"
            ) [0 .. width - 1]) ++ "\n"
        ) [0 .. height - 1]

solvePuzzle :: Symbolic SBool -> (Map String CW -> a) -> IO [a]
solvePuzzle prob fn = do
    res <- allSat prob
    return $ map fn (getModelDictionaries res)

-- Solves a battleship puzzle and prints the solution
battleship :: BattleshipInst -> IO ()
battleship puzzle = do
    res <- solvePuzzle (predicate puzzle) (getSolution puzzle)
    putStrLn $ (show $ length res) ++ " solution(s)"
    forM_ res $ \soln ->
        putStrLn $ soln

-- Won't work for puzzles with 10+ ship tiles in a column
battleshipParser :: Parser BattleshipInst
battleshipParser = do
    shipNums <- decimal `sepBy` (satisfy (\x -> isSpace x && x /= '\n'))
    endOfLine
    (grid, rowCounts) <- fmap unzip . many $ do
        row <- many1 cellParser
        skipSpace
        rowCount <- decimal
        endOfLine
        return (row, rowCount)
    colCounts <- many (subtract 48 . toInteger . ord <$> digit)
    return (shipNums, grid, rowCounts, colCounts)
    where
    cellParser :: Parser BattleshipInput
    cellParser =
        char8 'o' *> pure Circle
        <|> char8 'S' *> pure Square
        <|> char8 '>' *> pure FaceLeft
        <|> char8 '<' *> pure FaceRight
        <|> char8 'v' *> pure FaceUp
        <|> char8 '^' *> pure FaceDown
        <|> char8 '~' *> pure Wavy
        <|> char8 '.' *> pure NoInfo
