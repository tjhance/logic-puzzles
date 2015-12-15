module Slitherlink where

import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Data.Attoparsec.ByteString.Char8
import Data.Char (ord)
import Data.Maybe
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.SBV
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tuple
import Text.Printf

import Util

type SlitherlinkInst = [[Maybe Integer]]

{-- We represent a Slitherlink solution by a set of booleans corresponding to
    directed edges. The constraints will be:

    - An edge and its backedge cannot both be set.
    - For each set edge, there is an edge coming out of its target.
    - For each set edge, there is an edge entering its source (redundant).
    - For each vertex, at most one edge enters.
    - For each vertex, at most one edge leaves.
    - The number of edges around a square with a number is that number.
    - The edges form a single connected cycle (difficult).

    Encoding connectivity directly into the formula is very inefficient,
    so we use an incremental solving method instead. When a solution with
    multiple loops is returned, we add a clause with the negation of the
    complete loops that are present. After some number of iterations, the
    solution will have only one cycle.

    The current implementation is flawed in two ways:
    1) Only one solution will be returned, even if multiple exist.
    2) Whenever a solution with multiple cycles is returned, ALL of those cycles
       are marked as bad. It is possible for a puzzle to have significant space
       that is forced to be empty such that putting another cycle there would
       follow the rest of the rules. If the two-cycle solution is returned first
       then the correct solution will fail to be found.
--}

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = map ((,) x) xs ++ pairs xs

type Vertex = (Int, Int)
type Edge = (Vertex, Vertex)

rules :: SlitherlinkInst -> [[Edge]] -> Symbolic SBool
rules inst badCycles = do
    let height = length inst
        width = length (head inst)
        edgeLocs =
            [((r, c), (r, c+1)) | r <- [0..height], c <- [0..width-1]]
            ++ [((r, c), (r, c-1)) | r <- [0..height], c <- [1..width]]
            ++ [((r, c), (r+1, c)) | r <- [0..height-1], c <- [0..width]]
            ++ [((r, c), (r-1, c)) | r <- [1..height], c <- [0..width]]
        vertLocs =
            [(r, c) | r <- [0..height], c <- [0..width]]
        neighborVerts (r, c) =
            catMaybes
                [ if r > 0 then Just (r-1, c) else Nothing
                , if r < height then Just (r+1, c) else Nothing
                , if c > 0 then Just (r, c-1) else Nothing
                , if c < width then Just (r, c+1) else Nothing
                ]
        edgesInto v = [(v', v) | v' <- neighborVerts v]
        edgesOutOf v = [(v, v') | v' <- neighborVerts v]
        edgesAround (r, c) =
            [ ((r, c), (r+1, c))
            , ((r+1, c), (r+1, c+1))
            , ((r+1, c+1), (r, c+1))
            , ((r, c+1), (r, c))
            , ((r, c), (r, c+1))
            , ((r, c+1), (r+1, c+1))
            , ((r+1, c+1), (r+1, c))
            , ((r+1, c), (r, c))
            ]

    edgeVars <- forM edgeLocs $ \e ->
        symbolic ("edge-" ++ show e)
    let edges = Map.fromList (zip edgeLocs edgeVars)

    addConstraints $ do
        -- An edge and its backedge cannot be set
        forM_ edgeLocs $ \e -> do
            let e' = swap e
                v = edges ! e
                v' = edges ! e'
            addConstraint $ bnot (v &&& v')
        -- For each set edge, there is an edge coming out of its target.
        forM_ edgeLocs $ \e -> do
            let t = snd e
                possibleOuts = edgesOutOf t
                possibleOutVars = map (edges !) possibleOuts
                v = edges ! e
            addConstraint $
                v ==> bOr possibleOutVars
        -- For each set edge, there is an edge entering its source.
        forM_ edgeLocs $ \e -> do
            let s = fst e
                possibleIns = edgesInto s
                possibleInVars = map (edges !) possibleIns
                v = edges ! e
            addConstraint $
                v ==> bOr possibleInVars
        -- For each vertex, at most one edge enters.
        forM_ vertLocs $ \v -> do
            forM_ (pairs (edgesInto v)) $ \(e1, e2) ->
                let v1 = edges ! e1
                    v2 = edges ! e2
                in
                addConstraint $ bnot (v1 &&& v2)
        -- For each vertex, at most one edge leaves.
        forM_ vertLocs $ \v -> do
            forM_ (pairs (edgesOutOf v)) $ \(e1, e2) ->
                let v1 = edges ! e1
                    v2 = edges ! e2
                in
                addConstraint $ bnot (v1 &&& v2)
        -- For each square with a number, it has that many set edges around it.
        forM_ (zip [0..] inst) $ \(r, row) ->
            forM_ (zip [0..] row) $ \(c, cell) ->
                case cell of
                    Nothing -> pure ()
                    Just n -> do
                        let vars = map (edges !) (edgesAround (r, c))
                        addConstraint $
                            sum (map (\v -> ite v 1 0) vars) .== literal n
        -- Disallow any bad cycles that have shown up in the past.
        forM_ badCycles $ \cyc -> do
            let es = map (edges !) cyc
            addConstraint $ bnot (bAnd es)

cycles :: SlitherlinkInst -> Map Edge Bool -> [[Edge]]
cycles inst sol =
    fst $ foldl (\(cycs, vis) e ->
        if not (sol ! e) || e `Set.member` vis
        then (cycs, vis)
        else
            let (cyc', vis') = followCycle inst sol e vis
            in (cyc':cycs, vis')
    ) ([], Set.empty) edgeLocs
    where
    height = length inst
    width = length (head inst)
    edgeLocs =
        [((r, c), (r, c+1)) | r <- [0..height], c <- [0..width-1]]
        ++ [((r, c), (r, c-1)) | r <- [0..height], c <- [1..width]]
        ++ [((r, c), (r+1, c)) | r <- [0..height-1], c <- [0..width]]
        ++ [((r, c), (r-1, c)) | r <- [1..height], c <- [0..width]]

followCycle :: SlitherlinkInst -> Map Edge Bool -> Edge -> Set Edge -> ([Edge], Set Edge)
followCycle inst sol e visited =
    go e [] visited
    where
    height = length inst
    width = length (head inst)
    neighborVerts (r, c) =
        catMaybes
            [ if r > 0 then Just (r-1, c) else Nothing
            , if r < height then Just (r+1, c) else Nothing
            , if c > 0 then Just (r, c-1) else Nothing
            , if c < width then Just (r, c+1) else Nothing
            ]
    edgesOutOf v = [(v, v') | v' <- neighborVerts v]
    go e acc vis =
        if e `Set.member` vis
        then
            (reverse acc, vis)
        else
            case filter (sol !) (edgesOutOf (snd e)) of
                [] -> error (printf "Edge %s without a following edge." (show e))
                e':[] -> go e' (e:acc) (Set.insert e vis)
                _ -> error "Edge with multiple following edges."

getSolution :: SlitherlinkInst -> Map String CW -> String
getSolution inst m =
    let height = length inst
        width = length (head inst)
        edgeName e = "edge-" ++ show e
    in
    execWriter $ do
        forM_ [0..height] $ \r -> do
            forM_ [0..width-1] $ \c -> do
                tell "+"
                let e = ((r, c), (r, c+1))
                    e' = swap e
                if (fromCW (m ! edgeName e) || fromCW (m ! edgeName e'))
                    then tell "-"
                    else tell " "
            tell "+\n"
            when (r /= height) $ do
                forM_ [0..width] $ \c -> do
                    let e = ((r, c), (r+1, c))
                        e' = swap e
                    if (fromCW (m ! edgeName e) || fromCW (m ! edgeName e'))
                        then tell "|"
                        else tell " "
                    -- TODO: Display numbers in solution output
                    when (c /= width) $ tell " "
                tell "\n"

solvePuzzle :: SlitherlinkInst -> (Map String CW -> a) -> IO a
solvePuzzle inst fn = go []
    where
    height = length inst
    width = length (head inst)
    edgeLocs =
        [((r, c), (r, c+1)) | r <- [0..height], c <- [0..width-1]]
        ++ [((r, c), (r, c-1)) | r <- [0..height], c <- [1..width]]
        ++ [((r, c), (r+1, c)) | r <- [0..height-1], c <- [0..width]]
        ++ [((r, c), (r-1, c)) | r <- [1..height], c <- [0..width]]
    edgeName e = "edge-" ++ show e
    go badCycs = do
        let pred = rules inst badCycs
        res <- sat pred
        let m = getModelDictionary res
            sol = Map.fromList (map (\e -> (e, fromCW (m ! edgeName e))) edgeLocs)
            resCycles = cycles inst sol
        case resCycles of
            [] -> pure (fn (getModelDictionary res))
            c:[] -> pure (fn (getModelDictionary res))
            _ -> go (resCycles ++ badCycs)

slitherlink :: SlitherlinkInst -> IO ()
slitherlink puzzle = do
    res <- solvePuzzle puzzle (getSolution puzzle)
    putStrLn res

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
