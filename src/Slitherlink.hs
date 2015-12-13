{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}

module Slitherlink where

import Control.Applicative
import Control.Monad.Writer
import Data.Attoparsec.ByteString (Parser)
import Data.Attoparsec.ByteString.Char8
import Data.Char (ord)
import Data.SBV
import Data.Generics
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Printf

import Util

type SlitherlinkInst = [[Maybe Integer]]

{-- Model of the space of Slitherlink solutions
    Each cell is either inside the solution curve or outside. The edges
    that are to be drawn are those on the boundary between an Inside cell and
    an Outside cell.

    It is not clear if there is a way to encode the fact that there is only one loop
    that is easy for the SMT solver to work with, so we'll leave that constraint out
    and check that condition in post-processing. Each solution returned by the SMT
    solver will consist of nonintersecting loops, but there may be more than one.
--}
data CellType = Inside | Outside deriving (Show, Read, Eq, Ord, Data, SymWord, HasKind)
type CellState = SBV CellType

pairs :: Ord a => [a] -> [(a, a)]
pairs l = [(x, y) | x <- l, y <- l, x <= y]

numDifferent :: CellState -> [CellState] -> Word8 -> SBool
numDifferent center nbrs target =
    (sum (map (\cell ->
        ite (cell ./= center)
            (literal 1)
            (literal 0)
    ) nbrs)) .== literal target

rules :: SlitherlinkInst -> Symbolic SBool
rules inst = do
    let height = length inst
    let width = length (head inst)

    -- We create a border around the puzzle that is entirely outside cells.
    let positions = [(r, c) | r <- [0 .. height+1], c <- [0 .. width+1]]
    let neighbors (r, c) =
            catMaybes
                [ if r > 0 then Just (r-1, c) else Nothing
                , if r <= height then Just (r+1, c) else Nothing
                , if c > 0 then Just (r, c-1) else Nothing
                , if c <= width then Just (r, c+1) else Nothing
                ]

    board <-
        forM positions $ \p ->
            symbolic ("cell-" ++ show p)
    let cells = Map.fromList (zip positions board)

    addConstraints $ do
        -- Extra cells must all be Outside
        forM_ [0 .. width + 1] $ \c -> do
            let topCell = cells ! (0, c)
                botCell = cells ! (height+1, c)
            addConstraint $ topCell .== literal Outside
            addConstraint $ botCell .== literal Outside
        forM_ [0 .. height + 1] $ \r -> do
            let leftCell = cells ! (r, 0)
                rightCell = cells ! (r, width+1)
            addConstraint $ leftCell .== literal Outside
            addConstraint $ rightCell .== literal Outside
        -- Forbid any patterns of the form
        -- X.
        -- .X
        -- This corresponds to a place where the path would cross itself.
        forM_ [0 .. height] $ \r -> do
            forM_ [0 .. width] $ \c -> do
                let c11 = cells ! (r, c)
                    c12 = cells ! (r, c+1)
                    c21 = cells ! (r+1, c)
                    c22 = cells ! (r+1, c+1)
                addConstraint $ (c11 ./= c22) ||| (c21 ./= c12) ||| (c11 .== c12)
        -- Constraints from the actual puzzle grid
        forM_ (zip [1..] inst) $ \(r, row) ->
            forM_ (zip [1..] row) $ \(c, inp) ->
                case inp of
                    Nothing -> pure ()
                    Just n -> do
                        let nbrs = map (cells !) (neighbors (r, c))
                        let cell = cells ! (r, c)
                        addConstraint $ numDifferent cell nbrs (fromInteger n)

readSolution :: SlitherlinkInst -> Map String CW -> Map (Int, Int) CellType
readSolution inst m =
    let height = length inst
        width = length (head inst)
    in
    Map.fromList [((r, c), fromCW (m ! ("cell-" ++ show (r, c)))) | r <- [0 .. height+1], c <- [0 .. width+1]]

floodfill :: Map (Int, Int) CellType -> (Int, Int) -> Set (Int, Int)
floodfill m p = go p (Set.singleton p)
    where
    sourceType = Map.lookup p m
    neighbors (r, c) = [(r-1, c), (r+1, c), (r, c-1), (r, c+1)]
    go p acc =
        foldl (\acc n ->
            if Map.lookup n m == sourceType && not (Set.member n acc)
            then go n (Set.insert n acc)
            else acc
        ) acc (neighbors p)

checkSolution :: Map (Int, Int) CellType -> Bool
checkSolution m =
    let firstInside = fst . head . filter ((== Inside) . snd) . Map.toList $ m
        firstOutside = fst . head . filter ((== Outside) . snd) . Map.toList $ m
        insideSet = floodfill m firstInside
        outsideSet = floodfill m firstOutside
    in
    all (\(k, _) -> k `Set.member` insideSet || k `Set.member` outsideSet) (Map.toList m)

-- Returns a string representation of the result
getSolution :: SlitherlinkInst -> Map String CW -> String
getSolution inst m =
    let height = length inst
        width = length (head inst)
    in
    concat $ map (\r ->
        (concat $ map (\c ->
            let cell = fromCW (m ! ("cell-" ++ show (r, c))) :: CellType
            in if cell == Inside then "X" else "."
        ) [1 .. width]) ++ "\n"
    ) [1 .. height]

solvePuzzle :: Symbolic SBool -> (Map String CW -> Bool) -> (Map String CW -> a) -> IO [a]
solvePuzzle prob check fn = do
    res <- allSat prob
    return $ map fn . filter check $ getModelDictionaries res

slitherlink :: SlitherlinkInst -> IO ()
slitherlink puzzle = do
    res <- solvePuzzle (rules puzzle) (checkSolution . readSolution puzzle) (getSolution puzzle)
    printf "%d solution(s)\n" (length res)
    forM_ res $ \soln ->
        putStrLn soln

-- Note that there needs to be an empty line to signal the end of the puzzle.
slitherlinkParser :: Parser SlitherlinkInst
slitherlinkParser = do
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
        <|> (char '.' *> pure Nothing)
        <|> (char '_' *> pure Nothing)
