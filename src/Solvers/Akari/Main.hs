module Main where

import Akari
import Data.Attoparsec.ByteString
import Data.ByteString.Char8
import System.IO (isEOF)
import Text.Printf

parseLoop :: (a -> IO ()) -> Parser a -> IO ()
parseLoop callback parser =
    go (parse parser)
    where
    go cont = do
        eof <- isEOF
        if eof then pure () else do
            line <- flip snoc '\n' <$> Data.ByteString.Char8.getLine
            case cont line of
                Fail _ _ e -> do
                    printf "Parse failed: %s\n" (show e)
                    go (parse parser)
                Partial cont' -> go cont'
                Done _ x -> do
                    printf "Working...\n"
                    callback x
                    go (parse parser)

main :: IO ()
main = parseLoop akari akariParser
