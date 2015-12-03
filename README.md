# Solving logic puzzles using an SMT solver

Some examples of solving various logic puzzles in Haskell. The examples
use the SBV library in Haskell, which in turn uses the Z3 solver.

Puzzles solved here include
 - Sudoku
 - Battleship
 - Paint By Numbers

## Installing

You'll need Z3 installed. I used version
[4.3.2](https://github.com/Z3Prover/z3/releases/tag/z3-4.3.2),
and I couldn't get SBV to work with version 4.3.1.
(I didn't try any other versions. Also, I think
SBV works with some other solvers too, but I also didn't try those.)

Once you've got Z3 working, you can install all the Haskell dependencies
and run with

```
cabal install
cabal run
```

## Explanation

The idea is to use the general constraint solver to solve logic puzzles.
This makes it easy to write programs for new puzzles, since you basically
just have to code the rules of the game rather than an algorithm for
solving it.

There's a tradeoff in speed, here. If you wrote a specialized solver
for a specific puzzle, your solver could be a lot faster. (It's also
possible that the SBV implementations I've included here could be
optimized by expressing the rules better, but I didn't spend a lot
of time doing that.)

To demonstrate the general idea, let's take a look at how we implemented Sudoku,
one of the simplest of our puzzles. (From `src/Sudoku.hs`).

We start with a type that represents an _instance_ of a Sudoku puzzle.
A Sudoku puzzle instance is a 9x9 grid where some entries have a number in them.

```haskell
type SudokuInst = [[Maybe Integer]]
```

The meat will be a function called `rules`, which creates variables representing
the solution to the puzzle and adds constraints.

```haskell
rules inst :: Symbolic SBool
```

`Symbolic` is a monad defined by the SBV library. It represents a computation
that can create variables. So this computation will create variables and return
a boolean-valued expression in terms of those variables. Let's begin:

```haskell
rules inst = do
    board <-
        forM [0..8] $ \x ->
            forM [0..8] $ \y ->
                (symbolic (show x ++ "-" ++ show y) :: Symbolic SWord32)
```

This creates the "board" which is just 9 * 9 integer variables to represent
the solution.

Now we add constraints! First, we just constrain the numbers to match the input
numbers in cells where there is some input.

```haskell
    addConstraints $ do
        -- constraint to match input
        forM_ (zip inst board) $ \(instRow, boardRow) ->
            forM_ (zip instRow boardRow) $ \(instCell, var) ->
                do
                    case instCell of Nothing -> return ()
                                     Just x -> addConstraint $ var .== (literal (fromIntegral x))
```

The `.==` operator you see is for comparing SBV values. The other operators we
use in this program are `.>=`, `.<=`, `./=`, `&&&`, and `|||`.

Now we have to do the constraints for a general sudoku board. Every number must
be between 1 and 9 (well, between 0 and 8 here, because we zero-index).

```haskell
        forM_ (zip inst board) $ \(instRow, boardRow) ->
            forM_ (zip instRow boardRow) $ \(instCell, var) ->
                addConstraint $ var .>= 0 &&& var .<= 8
```

Finally, we constrain every row, column, and 3x3 squares to have unique entries.
I wasn't sure the "best" way to do that; I ended up just
 - asserting that no two values in the same row/col/square are equal
 - asserting that for each value 0-8, at least one of the entries in that row/col/square
   has that value.
(These rules roughly correspond to the two main rules humans use to solve
Sudoku, and since humans are generally able to solve Sudoku, it seems like a good
idea to include them.)

```haskell
        let constraint1Through9 vars = do
                -- for each `value`, at least one value in the {row,col,square} must be `value`
                forM_ [0..8] $ \value ->
                    addConstraint $
                        foldl (|||) (literal False) $ map (\var -> var .== literal value) vars
                -- none of the values are equal
                -- (technically redundant but maybe this will help the solver?)
                forM_ (allPairs vars) $ \(v1, v2) -> addConstraint $ v1 ./= v2

        forM_ board $ \row ->
            constraint1Through9 row

        forM_ (transpose board) $ \col ->
            constraint1Through9 col

        -- getSquares is a utility function which groups the cells by which
        -- 3x3 subsquare they are in.
        forM_ (getSquares board) $ \sqr ->
            constraint1Through9 sqr
```

See `src/Sudoku.hs` for all all the code including the boilerplate used to actually put
this through the solver.
