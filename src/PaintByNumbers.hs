module PaintByNumbers where

import Data.SBV
import Data.List (transpose)
import Data.Traversable (forM)
import Control.Monad (forM_)
import Data.Map (Map, (!))
import Debug.Trace

import Util

type PBNInst = ([[Int]], [[Int]])

predicate :: PBNInst -> Symbolic SBool
predicate inst = do
    let (rowNums, colNums) = inst
    let height = length rowNums
    let width = length colNums

    board <-
        forM [0 .. height-1] $ \r ->
            forM [0 .. width-1] $ \c -> do
                symbolic ("cell-" ++ show r ++ "-" ++ show c) :: Symbolic SBool
    
    let constrainRow :: [SBool] -> [Int] -> Symbolic SBool
        constrainRow cells contiguousCounts = do
            let prefixSums = map (\i -> sum (take i contiguousCounts) + i) [0 .. length contiguousCounts]
            let startNum = 0
            let endNum = if length contiguousCounts == 0 then 0 else (last prefixSums) - 1
            let fillNums = concat $ map (\(prefixSum, contiguousCount) ->
                    [(prefixSum + i, prefixSum + i + 1) | i <- [0 .. contiguousCount - 1]]
                  ) (zip prefixSums contiguousCounts)
            let noFillNums = concat $ map (\prefixSum ->
                    if prefixSum == 0 then
                        [(0, 0)]
                    else if prefixSum == endNum + 1 then
                        [(prefixSum - 1, prefixSum - 1)]
                    else
                        [(prefixSum - 1, prefixSum), (prefixSum, prefixSum)]
                  ) prefixSums

            progressNumbers <- forM [0 .. length cells] $ \_ -> (free_ :: Symbolic SWord8)

            addConstraints $ do
                addConstraint $ head progressNumbers .== literal (fromIntegral 0)
                addConstraint $ last progressNumbers .== literal (fromIntegral endNum)
                forM_ (zip3 cells progressNumbers (tail progressNumbers)) $ \(cell, p1, p2) ->
                    addConstraint $
                        (cell &&&
                        (foldl (|||) false
                            (map (\(i, j) -> p1 .== literal (fromIntegral i) &&&
                                             p2 .== literal (fromIntegral j)) fillNums)))
                        |||
                        (cell .== literal False &&&
                        (foldl (|||) false
                            (map (\(i, j) -> p1 .== literal (fromIntegral i) &&&
                                             p2 .== literal (fromIntegral j)) noFillNums)))

    c1 <- forM (zip rowNums board) $ \(counts, vars) -> constrainRow vars counts
    c2 <- forM (zip colNums $ transpose board) $ \(counts, vars) -> constrainRow vars counts

    return $ foldl (&&&) (literal True) (c1 ++ c2)

getSolution :: PBNInst -> Map String CW -> String
getSolution inst m =
    let (rowCounts, colCounts) = inst
        height = length rowCounts
        width = length colCounts
    in
        concat $ map (\r ->
            (concat $ map (\c ->
                let val = fromCW (m ! ("cell-" ++ show r ++ "-" ++ show c)) :: Bool
                in if val then "O" else "."
            ) [0 .. width - 1]) ++ "\n"
        ) [0 .. height - 1]

solvePuzzle :: Symbolic SBool -> (Map String CW -> a) -> IO [a]
solvePuzzle prob fn = do
    res <- allSat prob
    return $ map fn (getModelDictionaries res)

pbn :: PBNInst -> IO ()
pbn puzzle = do
    res <- solvePuzzle (predicate puzzle) (getSolution puzzle)
    putStrLn $ (show $ length res) ++ " solution(s)"
    forM_ res $ \soln ->
        putStrLn $ soln
