{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}

module Battleship where

import Data.SBV hiding (constrain)
import Data.Generics
import Data.List (transpose)
import Data.Map (Map, (!))
import Data.Traversable (forM)
import Control.Monad (forM_)

import Util

data BattleshipInput = Circle
                     | Square
                     | FaceLeft
                     | FaceRight
                     | FaceUp
                     | FaceDown
                     | Wavy
                     | NoInfo

-- Number of each size of ship (e.g. [4, 3, 2, 1] in most games,
-- that is, 4 subs, 3 destryers, 2 cruisers, 1 battleship)
-- Input grid
type BattleshipInst = ([Integer], [[BattleshipInput]], [Integer], [Integer])

data CellType = Empty | Horiz | Vert deriving (Show, Read, Eq, Ord, Data, SymWord, HasKind)
type CellState = (SBV CellType, SWord8, SWord8)

isCellStateOkay :: BattleshipInput -> CellState -> SBool
isCellStateOkay NoInfo (ctype, i, n) = literal true
isCellStateOkay Wavy (ctype, i, n) = (ctype .== literal Empty)
isCellStateOkay Circle (ctype, i, n) = (ctype .== literal Horiz &&& i .== literal 0 &&& n .== literal 1)
isCellStateOkay Square (ctype, i, n) = (ctype ./= literal Empty &&& n .>= 2 &&& i ./= 0 &&& i ./= (n - 1))
isCellStateOkay FaceRight (ctype, i, n) = (ctype .== literal Horiz &&& i .== literal 0 &&& n .>= literal 2)
isCellStateOkay FaceLeft (ctype, i, n) = (ctype .== literal Horiz &&& i .== (n - literal 1) &&& n .>= literal 2)
isCellStateOkay FaceDown (ctype, i, n) = (ctype .== literal Vert &&& i .== 0 &&& n .>= literal 2)
isCellStateOkay FaceUp (ctype, i, n) = (ctype .== literal Vert &&& i .== (n - literal 1) &&& n .>= literal 2)

baseCellConstraint :: Word8 -> CellState -> SBool
baseCellConstraint maxShipSize (ctype, i, n) =
    (ctype .== literal Empty &&& i .== literal 0 &&& n .== literal 0) |||
    (ctype .== literal Horiz &&& literal 0 .<= i &&& i .< n &&& literal 1 .<= n &&& n .<= literal maxShipSize) |||
    (ctype .== literal Vert &&& literal 0 .<= i &&& i .< n &&& literal 2 .<= n &&& n .<= literal maxShipSize)

constrainHorizontallyAdj :: CellState -> CellState -> SBool
constrainHorizontallyAdj = constrainAdj Horiz Vert

constrainVerticallyAdj :: CellState -> CellState -> SBool
constrainVerticallyAdj = constrainAdj Vert Horiz

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

constrainFirst :: CellType -> CellType -> CellState -> SBool
constrainFirst horiz vert (ctype, i, n) =
    (ctype .== literal Empty) ||| (ctype .== literal vert) |||
    (ctype .== literal horiz &&& i .== literal 0)

constrainLast :: CellType -> CellType -> CellState -> SBool
constrainLast horiz vert (ctype, i, n) =
    (ctype .== literal Empty) ||| (ctype .== literal vert) |||
    (ctype .== literal horiz &&& i .== n - literal 1)

constrainDiagonallyAdj :: CellState -> CellState -> SBool
constrainDiagonallyAdj (ctype1, i1, n1) (ctype2, i2, n2) =
    ctype1 .== literal Empty |||
    ctype2 .== literal Empty

nonempty :: CellState -> SBool
nonempty (ctype, i, n) = ctype ./= literal Empty

numNonemptyInRow :: [CellState] -> Word8 -> SBool
numNonemptyInRow cells target =
    sum (map (\cell -> ite (nonempty cell) (literal 1) (literal 0)) cells) .== literal target

numOfShipsIs :: [[CellState]] -> Word8 -> Word8 -> SBool
numOfShipsIs cells shipSize numShips =
    (sum (map (\(ctype, i, n) ->
        ite (i .== literal 0 &&& n .== literal shipSize)
            (literal 1)
            (literal 0)
    ) (concat cells))) .== literal numShips

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
                constrain $ baseCellConstraint (fromIntegral maxShipSize) cell
                constrain $ isCellStateOkay input cell

        forM_ (allHorizPairs board) $ \(a, b) -> constrain $ constrainHorizontallyAdj a b
        forM_ (allVertPairs board) $ \(a, b) -> constrain $ constrainVerticallyAdj a b
        forM_ (allDiagPairs board) $ \(a, b) -> constrain $ constrainDiagonallyAdj a b
        forM_ (allLeft board) $ \a -> constrain $ constrainFirst Horiz Vert a
        forM_ (allTop board) $ \a -> constrain $ constrainFirst Vert Horiz a
        forM_ (allRight board) $ \a -> constrain $ constrainLast Horiz Vert a
        forM_ (allBot board) $ \a -> constrain $ constrainLast Vert Horiz a

        forM_ (zip rowCounts board) $ \(rowCount, row) ->
            constrain $ numNonemptyInRow row (fromIntegral rowCount)
        forM_ (zip colCounts (transpose board)) $ \(colCount, col) ->
            constrain $ numNonemptyInRow col (fromIntegral colCount)

        forM_ (zip [1..] instShipTypes) $ \(shipSize, numShips) ->
            constrain $ numOfShipsIs board (fromIntegral shipSize) (fromIntegral numShips)

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

battleship :: BattleshipInst -> IO ()
battleship puzzle = do
    res <- solvePuzzle (predicate puzzle) (getSolution puzzle)
    putStrLn $ (show $ length res) ++ " solution(s)"
    forM_ res $ \soln ->
        putStrLn $ soln
