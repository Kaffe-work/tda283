module Main where

import TypeChecker
import Javalette.ErrM

main :: Program -> Err Program
main [] = fail "No program to validate"
main prog = do
    result <- typecheck prog
    case result of
        Ok _ -> return "OK"
        Bad string -> return string