module Util where

import Data.SBV hiding (constrain)
import Control.Monad.Writer

type ConstraintAdder = WriterT [SBool] Symbolic ()
addConstraints :: ConstraintAdder -> Symbolic SBool
addConstraints constraintAdder = do
    ((), bools) <- runWriterT constraintAdder
    return $ foldl (&&&) (literal True) bools

constrain :: SBool -> ConstraintAdder
constrain x = tell [x]
