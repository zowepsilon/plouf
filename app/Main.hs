module Main where

import System.Environment

import Parser
import Typer

main :: IO ()
main = do
    args <- getArgs
    source <- readFile (args !! 0)
    case parseProgram source of
        Nothing -> putStrLn "parsing error"
        Just stmts -> do
            result <- runProgram emptyState stmts
            case result of
                Left err -> putStrLn $ "typing error: " ++ show err
                Right _ -> return ()
