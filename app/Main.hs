module Main where

import Parser
import Typer

main :: IO ()
main = do
    source <- readFile "test.plf"
    case parseProgram source of
        Nothing -> putStrLn "parsing error"
        Just stmts -> case runProgram emptyState stmts of
            Left err -> putStrLn $ "typing error: " ++ show err
            Right st -> print st
