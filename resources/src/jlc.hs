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
        Bad err -> hPutStrLn stderr err
        Ok tree -> do
            case typecheck tree of
                Bad string -> do
                    hPutStrLn stderr "type error"
                    hPutStrLn stderr string
                    exitFailure
                Ok _ -> hPutStrLn stderr "ok"    
check _ = hPutStrLn stderr "bad program"


main :: IO ()
main = do 
    file <- getContents
    check file