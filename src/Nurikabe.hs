{-# LANGUAGE TupleSections #-}

module Nurikabe where

{-- Rules: https://en.wikipedia.org/wiki/Nurikabe_(puzzle)

    The puzzle is played on a typically rectangular grid of cells,
    some of which contain numbers. Cells are initially of unknown color,
    but can only be black or white. Two same-color cells are considered
    "connected" if they are adjacent vertically or horizontally, but
    not diagonally. Connected white cells form "islands", while connected
    black cells form the "sea".

    The challenge is to paint each cell black or white, subject to the following rules:

     - Each numbered cell is an island cell, the number in it is the number of cells in that island.
     - Each island must contain exactly one numbered cell.
     - There must be only one sea, which is not allowed to contain "pools", i.e. 2x2 areas of black cells.

--}

import Data.SBV
import Data.Attoparsec.ByteString (Parser)
import Data.Attoparsec.ByteString.Char8
import Data.Array
import Data.List (nub, sort)
import Data.Maybe (catMaybes, isJust)
import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.STRef
import Data.Map (Map)
import Data.ByteString.Char8 (pack)
import qualified Data.Map

import Util

-- An instance of the puzzle is just a grid of numbers, some of which will have
-- numbers.
type NurikabeInst = [[Maybe Int]]

rules :: NurikabeInst -> Symbolic SBool
rules inst = do
    let height = length inst
    let width = length (head inst)

    -- True will mean a 'white' cell.
    board <-
        forM [0 .. height-1] $ \r ->
            forM [0 .. width-1] $ \c -> do
                symbolic ("cell-" ++ show r ++ "-" ++ show c) :: Symbolic SBool

    
    addConstraints $ do
        forM_ (zip3 inst board [0..]) $ \(instRow, boardRow, x) ->
            forM_ (zip3 instRow boardRow [0..]) $ \(instCell, var, y) ->
                do
                    case instCell
                     of Nothing -> return ()
                        Just n -> do
                            addConstraint var -- var == True
                            addConstraint $ isOnePolyomino inst board (x, y) (polyominoEnumeration !! n)

        let numberSum :: Word8
            numberSum = (fromIntegral (sum (catMaybes (concat inst))))

        addConstraint $ (sum (map (\var -> ite var (literal 1) (literal 0)) (concat board))) .==
            literal numberSum

isOnePolyomino :: NurikabeInst -> [[SBool]] -> (Int, Int) -> [Polyomino] -> SBool
isOnePolyomino inst board (x0, y0) polys =
    orList $ catMaybes $ map polyToSBool polys
  where
    polyToSBool (interior, border) =
        case checkIsAllJust (map (coordToConstraint True) (filter (/= (0,0)) interior) ++ map (coordToConstraint False) border)
        of Just x -> Just ( andList x )
           Nothing -> Nothing

    checkIsAllJust [] = Just []
    checkIsAllJust ((Just x) : xs) = case checkIsAllJust xs
                                     of Just rest -> Just (x : rest)
                                        Nothing -> Nothing
    checkIsAllJust (Nothing : xs) = Nothing

    coordToConstraint :: Bool -> (Int, Int) -> Maybe SBool
    coordToConstraint val (x, y) =
        let x1 = x0 + x
            y1 = y0 + y
        in
            if x1 >= 0 && x1 < length board && y1 >= 0 && y1 < length (head board) then
              (
               if not (isJust ((inst !! x1) !! y1)) then
                  Just $ ((board !! x1) !! y1) .== literal val
               else
                  Nothing
              )
            else
                if val then Nothing else Just (literal True)

-- Polyomino logic.
-- First element of the pair is a list of tuples containing locations of the
-- the omino piecs.
-- The second element is the orthogoal borders.
type Polyomino = ([(Int, Int)], [(Int, Int)])

polyominoEnumeration :: [[Polyomino]]
polyominoEnumeration = map enumerate [0 .. ]
    where
        enumerate 0 = []
        enumerate 1 = [( [(0, 0)], [(-1, 0), (0, -1), (0, 1), (1, 0)] )]
        enumerate i =
            map addBorders $ makeUnique $ filter hasGenus0 $ concat $ map augment $ polyominoEnumeration !! (i - 1)

        addBorders :: [(Int, Int)] -> Polyomino
        addBorders poly = (poly,
            nub $
            filter (\coord -> not (coord `elem` poly)) $
            concat (map (\(x, y) -> [(x-1, y), (x+1, y), (x, y-1), (x, y+1)]) poly)
          )

        makeUnique :: [[(Int, Int)]] -> [[(Int, Int)]]
        makeUnique list = nub $ map sort list

        augment :: Polyomino -> [[(Int, Int)]]
        augment (interior, border) = map (\borderElem -> borderElem : interior) border

        hasGenus0 :: [(Int, Int)] -> Bool
        hasGenus0 boxes =
            let minX = minimum $ map fst boxes
                minY = minimum $ map snd boxes
                maxX = maximum $ map fst boxes
                maxY = maximum $ map snd boxes

                has :: (Int, Int) -> Bool
                has (x, y) = (x, y) `elem` boxes

                v = length $ filter (\(x, y) -> has (x-1, y-1) || has (x-1, y) || has (x, y-1) || has (x, y))
                        [(x, y) | x <- [minX .. maxX + 1], y <- [minY .. maxY + 1]]

                e = (length $ filter (\(x, y) -> has (x-1, y) || has (x, y))
                        [(x, y) | x <- [minX .. maxX + 1], y <- [minY .. maxY + 1]])
                    +
                    (length $ filter (\(x, y) -> has (x, y-1) || has (x, y))
                        [(x, y) | x <- [minX .. maxX + 1], y <- [minY .. maxY + 1]])

                f = 2 + e - v
            in f == length boxes + 1

isSetOfCellsConnected :: [(Int, Int)] -> Bool
isSetOfCellsConnected [] = True
isSetOfCellsConnected (coords@(firstCoord : _)) = runST $ do
    let minX = minimum $ map fst coords
    let minY = minimum $ map snd coords
    let maxX = maximum $ map fst coords
    let maxY = maximum $ map snd coords
    let bounds = ((minX, minY), (maxX, maxY))

    let isOnArray = array bounds [((i, j), (i, j) `elem` coords) | i <- [minX .. maxX], j <- [minY .. maxY]]
    visitedArray <- array bounds <$> (mapM (\coord -> (coord,) <$> newSTRef False) [(i,j) | i <- [minX .. maxX], j <- [minY .. maxY]])

    count <- newSTRef 1
    writeSTRef (visitedArray ! firstCoord) True
    l1 <- newSTRef [firstCoord]
    l2 <- newSTRef []

    whileTrue $ do
        l <- readSTRef l1
        let (x, y) = head l
        forM_ [(x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)] $ \(x1, y1)-> do
            if x1 >= minX && x1 <= maxX && y1 >= minY && y1 <= maxY then
                do
                    isAlreadyVisited <- readSTRef $ visitedArray ! (x1, y1)
                    let isOn = isOnArray ! (x1, y1)
                    if isOn && not isAlreadyVisited then
                        do
                            l2' <- readSTRef l2
                            writeSTRef l2 ((x1, y1) : l2')
                            writeSTRef (visitedArray ! (x1, y1)) True
                            count' <- readSTRef count
                            writeSTRef count (count' + 1)
                    else
                        return ()
            else
                return ()
        
        l1' <- readSTRef l1
        l2' <- readSTRef l2

        if l1' == [] then do
            writeSTRef l1 l2'
            writeSTRef l2 []
        else
            return ()

        return $ not (l1' == [] && l2' == [])

    finalCount <- readSTRef count
    return (finalCount == length coords)

whileTrue :: Monad m => m Bool -> m ()
whileTrue x = do
    continue <- x
    if continue then
        whileTrue x
    else
        return ()

getSolution :: NurikabeInst -> Map String CW -> String
getSolution puzzle m = concat $ map (++ "\n") $ map concat $
    map (\i ->
        map (\j ->
            if (fromCW $ m Data.Map.! ("cell-" ++ show i ++ "-" ++ show j) :: Bool) then
                " "
            else
                "."
        ) [0 .. length (head puzzle) - 1]
    ) [0 .. length puzzle - 1]

solvePuzzle :: Symbolic SBool -> (Map String CW -> a) -> IO [a]
solvePuzzle prob fn = do
    res <- allSat prob
    return $ map fn (getModelDictionaries res)

nurikabe :: NurikabeInst -> IO ()
nurikabe puzzle = do
    res <- solvePuzzle (rules puzzle) (getSolution puzzle)
    putStrLn $ (show $ length res) ++ " solutions(s)"
    forM_ res $ \soln ->
        putStrLn $ soln

nurikabeParser :: Parser NurikabeInst
nurikabeParser =
    many1 ((cellParser `sepBy` (satisfy (\x -> isSpace x && x /= '\n'))) <* endOfLine)
    <* (string (pack "end"))
  where
    cellParser :: Parser (Maybe Int)
    cellParser = (char '.' *> return Nothing) <|> (Just <$> decimal)
