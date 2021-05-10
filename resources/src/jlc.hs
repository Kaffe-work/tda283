import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.Process     (callProcess)
import System.IO          (stderr, hPutStr)

import Alpha
import Javalette.Par  
import Javalette.ErrM 
import Javalette.Abs  (Program)
import Typechecker    --(typecheck)
import CompileLLVM       --(compile, toLLVM)

import Javalette.Print (printTree)

import qualified Annotated as A (Prog)

main :: IO ()
main = () <$
  (getContents >>= parse >>= check >>= putStrLn . toLLVM . compile)

-- | Parse file contents into AST.
parse :: String -> IO Program
parse s =
  case pProgram (myLexer s) of
    Bad err  -> do
      hPutStr stderr $ "ERROR : " <> err
      exitFailure
    Ok tree -> return tree

-- | Type check and return a type-annotated program.
check :: Program -> IO ()
check tree =
  case typecheck tree of
    Bad err -> do
      putStrLn $ printTree tree
      hPutStr stderr $ "ERROR : " <> err
      exitFailure
    Ok tree' -> hPutStr stderr "OK\n" >> return tree'

--α :: A.Prog -> IO A.Prog
--α tree = let tree' = α_rename tree in
--             return tree'

{--
check :: String -> IO ()
check prog = do
    case pProgram (myLexer prog) of
        Bad err -> do 
           hPutStrLn stderr "ERROR"
           exitFailure
        Ok tree -> do
            case typecheck tree of
                Bad string -> do
                    hPutStrLn stderr "ERROR"
                    exitFailure
                Ok _ -> hPutStrLn stderr "OK"    
check _ = hPutStrLn stderr "bad program"


main :: IO ()
main = do 
    file <- getContents
    check file
--}