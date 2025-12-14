module Main where

import Data.Char
import System.Environment
import System.IO
import GHC.Utils.Misc

import Parser
import Typer

fileRun :: String -> IO ()
fileRun fileName = do
    source <- readFile fileName
    case parseProgram source of
        Nothing -> putStrLn "parsing error"
        Just stmts -> do
            result <- runProgram emptyState stmts
            case result of
                Left err -> putStrLn $ "typing error: " ++ show err
                Right _ -> return ()

interactiveRun :: State -> IO ()
interactiveRun state = do
    putStr "plouf > "
    hFlush stdout
    firstLine <- getLine
    fragment <- prompt (reverse $ removeSpaces firstLine)
    case parseProgram fragment of
        Nothing -> putStrLn "parsing error"
        Just stmts -> do
            result <- runProgram state stmts
            case result of
                Left err -> do
                    putStrLn $ "typing error: " ++ show err
                    interactiveRun state
                Right state' ->
                    interactiveRun state'

    where
        prompt :: String -> IO String
        prompt (';' : ';' : rest) = return $ reverse ('\n' : rest)
        prompt input = do
            putStr "    ... "
            hFlush stdout
            line <- getLine
            if null line
                then do
                    putStr "\x1b[A"
                    hFlush stdout
                    return $ reverse ('\n' : input)
                else prompt $ (dropWhile isSpace $ reverse line) ++ ('\n' : input)
            

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> interactiveRun emptyState
        (fileName : _) -> fileRun fileName
