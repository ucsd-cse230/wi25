#!/usr/bin/env runhaskell

import System.Environment (getArgs)
import System.IO
import Control.Monad (when)
import Data.List (isInfixOf)

main :: IO ()
main = do
    args <- getArgs
    case args of
      [file] -> processFile file
      _      -> abortMessage

processFile :: FilePath -> IO ()
processFile inputFile = do
  content <- readFile inputFile
  let processedContent = unlines $ processLines $ lines content
  -- writeFile outputFile processedContent
  putStrLn processedContent

abortMessage :: IO b
abortMessage = do
  putStrLn "Usage: program input_file"
  fail "Incorrect number of arguments"

-- Process the lines of text according to the rules
processLines :: [String] -> [String]
processLines = go [] False False
  where
    go acc inCut inSorry [] = reverse acc
    go acc inCut inSorry (x:xs)
      | "START:CUT"   `isInfixOf` x = go acc True inSorry xs
      | "END:CUT"     `isInfixOf` x = go acc False inSorry xs
      | "START:SORRY" `isInfixOf` x = go acc inCut True xs
      | "END:SORRY"   `isInfixOf` x = go ("  sorry":acc) inCut False xs
      | inCut                       = go acc inCut inSorry xs
      | inSorry                     = go acc inCut inSorry xs
      | otherwise                   = go (x:acc) inCut inSorry xs
