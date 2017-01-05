{-# LANGUAGE TupleSections #-}

module Akari where

import Control.Applicative
import Data.Attoparsec.ByteString
import Data.Attoparsec.ByteString.Char8
import Data.Char (ord)
import Data.SBV
import Control.Monad.Writer
import Data.Map (Map, (!))
import Data.List (transpose)
import Data.Maybe (fromJust, catMaybes)

import Util

-- Akari (or Light Up)
-- Light Up is played on a rectangular grid of white and black cells.
-- The player places light bulbs in white cells such that no two bulbs shine on each other,
-- until the entire grid is lit up. A bulb sends rays of light horizontally and vertically,
-- illuminating its entire row and column unless its light is blocked by a black cell.
-- A black cell may have a number on it from 0 to 4, indicating how many bulbs must be
-- placed adjacent to its four sides; for example, a cell with a 4 must have four bulbs around it,
-- one on each side, and a cell with a 0 cannot have a bulb next to any of its sides.
-- An unnumbered black cell may have any number of light bulbs adjacent to it, or none.
-- Bulbs placed diagonally adjacent to a numbered cell do not contribute to the bulb count.


data AkariType = Wall | Space

type AkariInst = [[(AkariType, Maybe Integer)]]

type Elem = SWord32
type Row = [Elem]
type Board = [Row]

rules :: AkariInst -> Symbolic SBool
rules inst = do
    let width = length (head inst)
    let height = length inst

    board <-
        forM [0..height-1] $ \r ->
            forM [0..width-1] $ \c ->
                (symbolic (show r ++ "-" ++ show c) :: Symbolic SBool)

    let getVar r c = if r >= 0 && r < height && c >= 0 && c < width then Just $ (board !! r) !! c else Nothing

    addConstraints $ do
        forM_ (zip3 [0 .. ] inst board) $ \(r, instRow, boardRow) ->
            forM_ (zip3 [0 .. ] instRow boardRow) $ \(c, instCell, var) ->
                do
                    -- constraints to match input numbers

                    case instCell
                      of (_, Just i) -> do
                            -- number of bulbs adjacent to this square are correct
                            addConstraint $ literal i .==
                                (sum $ map (\var -> ite var (literal 1) (literal 0)) $
                                catMaybes $ [getVar (r+1) c, getVar (r-1) c, getVar r (c-1), getVar r (c+1)])
                         (_, Nothing) ->
                            return ()

                    -- general bulb constraints

                    case instCell
                      of (Wall, _) -> do
                            -- no bulb on a wall
                            addConstraint $ var .== literal False
                         (Space, _) -> do
                            -- this space is LIT
                            let visibleSpaceInclusive = getVisibleSpace inst (r, c)
                            addConstraint $ orList $ map (\(r, c) -> (board !! r) !! c) visibleSpaceInclusive 

                            -- this space cannot simulatenously have a bulb if it is otherwise lit
                            let visibleSpaceExclusive = filter (/= (r, c)) visibleSpaceInclusive
                            forM_ visibleSpaceExclusive $ \(r1, c1) -> do
                                addConstraint $ bnot $ var &&& ((board !! r1) !! c1)
  where
    getVisibleSpace inst (r, c) =
      let
        width = length (head inst)
        height = length inst
        getRun r c deltaR deltaC =
          let
            r1 = r + deltaR
            c1 = c + deltaC
            isSpace = if r1 >= 0 && c1 >= 0 && r1 < height && c1 < width then
                case (inst !! r1) !! c1 of (Wall, _) -> False
                                           (Space, _) -> True
                else False
          in
            if isSpace then (r1, c1) : getRun r1 c1 deltaR deltaC
                       else []
      in
        [(r,c)] ++ getRun r c 0 (-1) ++ getRun r c 0 1 ++ getRun r c 1 0 ++ getRun r c (-1) 0

getSolution :: AkariInst -> Map String CW -> String
getSolution inst m = 
  let
    width = length (head inst)
    height = length inst
  in
    concat $ map (++ "\n") $ map concat $
    map (\i ->
        map (\j ->
            if (fromCW $ m ! (show i ++ "-" ++ show j) :: Bool) then
                "+" -- light bulb
            else
                case ((inst !! i) !! j) of (_, Just i) -> show i
                                           (Space, Nothing) -> " "
                                           (Wall, Nothing) -> "#"
        ) [0..width-1]
    ) [0..height-1]

solvePuzzle :: Symbolic SBool -> (Map String CW -> a) -> IO [a]
solvePuzzle prob fn = do
    res <- allSat prob
    return $ map fn (getModelDictionaries res)

akari :: AkariInst -> IO ()
akari puzzle = do
    res <- solvePuzzle (rules puzzle) (getSolution puzzle)
    putStrLn $ (show $ length res) ++ " solution(s)"
    forM_ res $ \soln ->
        putStrLn $ soln

-- Note that there needs to be an empty line to signal the end of the puzzle.
akariParser :: Parser AkariInst
akariParser = do
    puz <- many $ do
        row <- many1 cellParser
        endOfLine
        pure row
    endOfLine
    pure puz
    where
    cellParser :: Parser (AkariType, Maybe Integer)
    cellParser =
        ((Wall,) . Just . subtract 48 . toInteger . ord <$> digit)
        <|> (char '#' *> pure (Wall, Nothing))
        <|> (char '.' *> pure (Space, Nothing))
