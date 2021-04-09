module Main where

import Control.Exception
import Javalette.Par (myLexer, pProgram)
import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.IO.Error    (isUserError, ioeGetErrorString)
import TypeChecker
import Javalette.ErrM
import System.IO
import Javalette.Abs

check :: String -> IO ()
check prog = do
    case pProgram (myLexer prog) of
        Bad err -> do 
           hPutStrLn stderr "ERROR"
           exitFailure
        Ok tree -> do
            case typecheck tree of
                Bad string -> do
                    hPutStrLn stderr string--"ERROR"
                    exitFailure
                Ok _ -> hPutStrLn stderr "OK"    
check _ = hPutStrLn stderr "bad program"


main :: IO ()
main = do 
    file <- getContents
    check file