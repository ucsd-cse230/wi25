#!/usr/bin/env runhaskell

{-# LANGUAGE OverloadedStrings #-}

import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.List (isInfixOf)
import Data.Char (isSpace)

separator :: String
separator = "@@@"

ext :: String
ext = "md"

codeStart :: String
codeStart = "```lean"

codeEnd ::String
codeEnd = "```"

main :: IO ()
main = do
  file:_ <- getArgs
  ls <- lines <$> readFile file
  let (ls', _)  = statefulMap step Code ls
  let out = format (concat ls')
  putStrLn out

  -- writeFile (file <> "." <> ext) out

statefulMap :: (s -> a -> (b, s)) -> s -> [a] -> ([b], s)
statefulMap f s [] = ([], s)
statefulMap f s (x:xs) =
    let (b, s')   = f s x
        (bs, s'') = statefulMap f s' xs
    in (b:bs, s'')

data Mode = Code | Lit deriving (Eq, Show)

format :: [(Mode, String)] -> String
format mls = unlines $ concat (formatBlock <$> blocks)
  where
    blocks = group mls

formatBlock :: (Mode, [String]) -> [String]
formatBlock (Lit, ls) = ls
formatBlock (Code, ls) = formatCodeBlock ls

formatCodeBlock :: [String] -> [String]
formatCodeBlock ls
  | null nonBlanks = ls
  | otherwise      = replicate startBlanks []
                   ++ [codeStart]
                   ++ nonBlanks
                   ++ [codeEnd]
                   ++ replicate endBlanks []
  where
    startBlanks = length $ takeWhile whitespace ls
    endBlanks   = length $ takeWhile whitespace $ reverse ls
    nonBlanks   = dropWhile whitespace . reverse . dropWhile whitespace . reverse $ ls

group :: Eq k => [(k, v)] -> [(k, [v])]
group [] = []
group ((k,v):rest) =
    let (matching, others) = span (\(k',_) -> k == k') rest
        values = v : map snd matching
    in (k, values) : group others

step :: Mode -> String -> ([(Mode, String)], Mode)
step Lit l
  | separator `isInfixOf` l = ([], Code)
  | otherwise = ([(Lit, l)], Lit)
step Code l
  | separator `isInfixOf` l = ([], Lit)
  | otherwise = ([(Code, l)], Code)

nonWhitespace :: String -> Bool
nonWhitespace = any (not . isSpace)

whitespace :: String -> Bool
whitespace = all isSpace