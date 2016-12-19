module Util where

import Data.SBV
import Control.Monad.Writer
import Debug.Trace

type ConstraintAdder = WriterT [SBool] Symbolic ()
addConstraints :: ConstraintAdder -> Symbolic SBool
addConstraints constraintAdder = do
    ((), bools) <- runWriterT constraintAdder
    return $ foldl (&&&) (literal True) bools

addConstraint :: SBool -> ConstraintAdder
addConstraint x = trace (show x) $ tell [x]

orList :: [SBool] -> SBool
orList = foldl (|||) (literal False)

andList :: [SBool] -> SBool
andList = foldl (&&&) (literal True)
