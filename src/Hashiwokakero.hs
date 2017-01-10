{-# LANGUAGE TupleSections #-}

module Hashiwokakero where

import Control.Applicative
import Data.Attoparsec.ByteString
import Data.Attoparsec.ByteString.Char8
import Data.Char (ord)
import Data.SBV
import Control.Monad.Writer
import Data.Map (Map, (!))
import Data.List (transpose, findIndices)
import Data.Maybe (fromJust, catMaybes, isJust)

import Util

-- Hashiwokakero
-- Some cells have numbers. You draw "bridges" or edges horizontally and vertically
-- between numbered cells.
-- At most 2 bridges between any two cells.
-- The number is the number of edges on that cell.
-- Bridges cannot cross

type HashiwokakeroInst = [[Maybe Integer]]

type Edge = ((Int, Int), (Int, Int))

toVarName :: Edge -> String
toVarName ((x1, y1), (x2, y2)) = show x1 ++ "-" ++ show y1 ++ "-" ++ show x2 ++ "-" ++ show y2

allPairs :: [a] -> [(a,a)]
allPairs [] = []
allPairs (x:xs) = map (x,) xs ++ allPairs xs

pairIntersects :: Edge -> Edge -> Bool
pairIntersects ((x1, y1), (x2, y2)) ((x3, y3), (x4, y4)) =
    if x1 == x2 && y3 == y4 then
        inBetween x3 x1 x4 && inBetween y1 y3 y4
    else if x1 == x2 && y3 == y4 then
        inBetween y3 y1 y4 && inBetween x1 x3 x4
    else
        False
  where
    inBetween a b c = (a < b && b < c) || (c < b && b < a)

getEdges :: HashiwokakeroInst -> [Edge]
getEdges inst =
    getHorizontalEdges inst ++ map (\(r,c) -> (c,r)) (getHorizontalEdges (transpose inst))
  where
    getHorizontalEdges inst = concat $ map (\(r, row) ->
            map (\(c1, c2) -> ((r, c1), (r, c2))) (consecutivePairs (getIndices row))
        ) (zip [0..] inst)
    consecutivePairs [] = []
    consecutivePairs (x : xs) = zip (x : xs) xs
    getIndices row = findIndices isJust row

rules :: HashiwokakeroInst -> Symbolic SBool
rules inst = do
    let width = length (head inst)
    let height = length inst

    let edges = getEdges inst
    edgesWithVars <- forM edges $ \edge -> do
        var <- symbolic (toVarName edge)
        return (edge, var)

    addConstraints $ do
        forM_ edgesWithVars $ \(_, var) -> do
            addConstraint $ var .>= 0 &&& var .<= 2

        forM_ (filter (\((e1, _), (e2, _)) -> pairIntersects e1 e2) (allPairs edgesWithVars)) $ \((_, v1), (_, v2)) ->
            addConstraint $ v1 .== 0 ||| v2 .== 0

        forM_ [0..height-1] $ \r ->
            forM_ [0..width-1] $ \c -> 
                case (inst !! r) !! c
                    of Nothing -> return ()
                       Just i -> addConstraint $ literal i .== sum (map snd $ filter (\((p1, p2), _) -> p1 == (r,c) || p2 == (r,c)) edgesWithVars)

getSolution :: HashiwokakeroInst -> Map String CW -> String
getSolution inst m = 
  let
    width = length (head inst)
    height = length inst
    edges = getEdges inst

    getHoriz = getHorizVert (\(r1, c1) -> \(r2, c2) -> \(r3, c3) -> r1 == r2 && r2 == r3 && ((c1 < c2 && c2 < c3) || (c3 < c2 && c2 < c1)))
    getVert = getHorizVert (\(r1, c1) -> \(r2, c2) -> \(r3, c3) -> c1 == c2 && c2 == c3 && ((r1 < r2 && r2 < r3) || (r3 < r2 && r2 < r1)))

    getHorizVert fn r c =
        case (
            catMaybes $
            map (\edge ->
                case (fromCW (m ! toVarName edge) :: Word32)
                    of 0 -> Nothing
                       i -> Just i
            ) $ filter (\(p1, p2) -> fn p1 (r, c) p2) edges
        ) of x : _ -> Just x
             [] -> Nothing
  in
    concat (map (\r ->
        concat (map (\c ->
            case (inst !! r) !! c
                of Just i -> show i
                   Nothing ->
                        case getHoriz r c
                            of Just 2 -> "="
                               Just 1 -> "-"
                               Nothing ->
                                    case getVert r c
                                        of Just 2 -> "‖"
                                           Just 1 -> "|"
                                           Nothing -> " "
        ) [0 .. width-1]) ++ "\n"
    ) [0 .. height-1])

solvePuzzle :: Symbolic SBool -> (Map String CW -> a) -> IO [a]
solvePuzzle prob fn = do
    res <- allSat prob
    return $ map fn (getModelDictionaries res)

hashiwokakero :: HashiwokakeroInst -> IO ()
hashiwokakero puzzle = do
    res <- solvePuzzle (rules puzzle) (getSolution puzzle)
    putStrLn $ (show $ length res) ++ " solution(s)"
    forM_ res $ \soln ->
        putStrLn $ soln

-- Note that there needs to be an empty line to signal the end of the puzzle.
hashiwokakeroParser :: Parser HashiwokakeroInst
hashiwokakeroParser = do
    puz <- many $ do
        row <- many1 cellParser
        endOfLine
        pure row
    endOfLine
    pure puz
    where
    cellParser :: Parser (Maybe Integer)
    cellParser =
        (Just . subtract 48 . toInteger . ord <$> digit)
        <|> (char '#' *> pure (Nothing))
        <|> (char '.' *> pure (Nothing))
