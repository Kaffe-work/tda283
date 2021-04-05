module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace

import Javalette.Abs
import Javalette.Print
import Javalette.ErrM

type Env = (Sig, [Context])
type Sig = Map Ident ([Type], Type)
type Context = Map Ident Type

typecheck :: Program -> Err ()
typecheck (PDefs []) = Bad "Empty program"
typecheck (PDefs defs) = do
    let env = emptyEnv
    let env1 = addPreDefFun env
    env2 <- collectFcnSymbls env1 defs
    case lookupFun env2 (Ident "main") of
        Bad str -> Bad str
        _ -> checkDefs env2 defs    

addPreDefFun :: Env -> Env
addPreDefFun (sig, cxts) = do 
    let (sig1, cxts1) = (Map.insert (Ident "printInt") ([Int], Void) sig, cxts)
    let (sig2, cxts2) = (Map.insert (Ident "printDouble") ([Double], Void) sig1, cxts1)
    let (sig3, cxts3) = (Map.insert (Ident "readInt") ([], Int) sig2, cxts2)
    let (sig4, cxts4) = (Map.insert (Ident "readDouble") ([], Double) sig3, cxts3)
    let (sig5, cxts5) = (Map.insert (Ident "printString") ([Int], Void) sig4, cxts4)
    (sig5, cxts5)

collectFcnSymbls :: Env -> [Def] -> Err Env
collectFcnSymbls env [] = Ok env
collectFcnSymbls env (DFun typ (Ident "main") args _:defs) =
    if not (null args) || (typ /= Int) then 
        Bad "main must return type int and have no arguments"
    else do
        let listOfArgTypes = map collectTypeFrmArg args
        env' <- updateFun env (Ident "main") (listOfArgTypes, typ)
        collectFcnSymbls env' defs
collectFcnSymbls env (DFun typ id args _:defs) = do
    let listOfArgTypes = map collectTypeFrmArg args
    if Void `elem` listOfArgTypes
        then Bad "arguments cannot have have type void"
        else do
            env' <- updateFun env id (listOfArgTypes, typ)
            collectFcnSymbls env' defs


collectTypeFrmArg :: Arg -> Type
collectTypeFrmArg (ADecl typ _) = typ

checkDefs :: Env -> [Def] -> Err ()
checkDefs _ [] = Ok ()
checkDefs env (def:defs) = do
    checkDef env def
    checkDefs env defs

checkDef :: Env -> Def -> Err ()
checkDef env (DFun typ _ args stms) = do
    env1 <- newBlock' env
    env2 <- addArgsToEnv env1 args
    checkStms env2 stms typ
    return ()
    
addArgsToEnv :: Env -> [Arg] -> Err Env
addArgsToEnv env [] = return env
addArgsToEnv env (ADecl typ id:args) = 
    if typ == Void
        then Bad "Arguments cannot be of type void "
        else case updateVar env id typ of
            Ok env' -> addArgsToEnv env' args
            Bad str -> Bad str

evalIdents :: Env -> [Ident] -> Type -> Err Env
evalIdents env [] _ = Ok env
evalIdents env (id:ids) typ = case updateVar env id typ of
    Ok env' -> evalIdents env' ids typ
    Bad str -> Bad str


-- Auxillary functions on Env
lookupVar :: Env -> Ident -> Err Type
lookupVar (_, []) id = Bad $ "Variable " ++ show id ++ " not defined"
lookupVar (sig, cxt:cxts) id = case Map.lookup id cxt of
    Nothing         -> lookupVar (sig, cxts) id
    (Just value)    -> Ok value

lookupFun :: Env -> Ident -> Err ([Type], Type)
lookupFun (sig, _) id = case Map.lookup id sig of
    Nothing         -> Bad $ "Function with " ++ show id ++ " not defined"
    (Just value)    -> Ok value

updateVar :: Env -> Ident -> Type -> Err Env
updateVar (sig, cxt:cxts) id typ = case Map.lookup id cxt of
    Nothing   -> Ok (sig, Map.insert id typ cxt : cxts)
    Just _    -> Bad $ "Variable with id " ++ show id ++ " already defined in scope"

updateFun :: Env -> Ident -> ([Type], Type) -> Err Env
updateFun (sig, cxt) id (argTypes, retType) = case Map.lookup id sig of
    Nothing     -> Ok (Map.insert id (argTypes, retType) sig, cxt)
    (Just _)    -> Bad $ "Function with id " ++ show id ++ " already defined in scope"

newBlock :: Env -> Env
newBlock (sig, cxt) = (sig, Map.empty:cxt)

newBlock' :: Env -> Err Env
newBlock' (sig, cxt) = return (sig, Map.empty:cxt)

emptyEnv :: Env
emptyEnv = (Map.empty, []) 

checkExp :: Env -> Type -> Exp -> Err Type
checkExp env typ exp = do
    typ1 <- inferExp env exp
    if (typ1 == typ) || ((typ1 == Int) && (typ == Double)) then
        return typ
    else
        Bad $   "checkExp: Expected type " ++ printTree typ ++
                " but found type " ++ printTree typ1 ++ 
                " with value " ++ printTree exp

checkAssExp :: Env -> Type -> Exp -> Err Type
checkAssExp env varTyp exp = do
    case varTyp of
        Double -> do
            expType <- inferExp env exp
            if expType `elem` [Double, Int] then
                return varTyp
            else
                Bad $ "checkAssExp: Expected int or double but got " ++ printTree expType
        Int -> do
            expType <- inferExp env exp
            if expType == Int then
                return varTyp
            else
               Bad $ "checkAssExp: Expected int or double but got " ++ printTree expType
        Bool -> do
            expType <- inferExp env exp
            if expType == Bool then
                return varTyp
            else
                Bad $ "checkAssExp: Expected bool but got " ++ printTree expType
               
checkStms :: Env -> [Stm] -> Type -> Err Env
checkStms env stms typ = case stms of
    [] ->do
        return env
    x : rest -> do
        env' <- checkStm env typ x
        checkStms env' rest typ

checkStm :: Env -> Type -> Stm -> Err Env
checkStm env typ stm = case stm of
    SEmpty -> Ok env
    SBlock stms -> do
        let env1 = newBlock env
        case checkStms env1 stms typ of
            Ok env -> do
                let (sig, _:cxts) = env
                return (sig, cxts)
            Bad string -> Bad string
    SDecls typ1 items -> foldM (addItemFold typ1) env items 
        where addItemFold typ env item = addItem env typ item
    SAss id exp -> do
        typ1 <- lookupVar env id
        typ2 <- inferExp env exp
        if typ1 == typ2 then Ok env
        else Bad "mismatch operand types"
    SIncr id -> do
        typ1 <- lookupVar env id 
        if typ1 `elem` [Int, Double] then Ok env
        else Bad "Can only increment Int/Double"
    SDecr id -> do
        typ1 <- lookupVar env id 
        if typ1 `elem` [Int, Double] then Ok env
        else Bad "Can only increment Int/Double"
    SReturn exp -> do
        checkExp env typ exp
        return env
    SNoReturn -> Ok env
    SIf exp stm1 -> do
        checkExp env Bool exp
        let env1 = newBlock env
        case checkStm env1 typ stm1 of
            Ok env -> do
                let (sig, _:cxts) = env
                return (sig, cxts)
            Bad string -> Bad string
    SIfElse exp stm1 stm2 -> do
        checkExp env Bool exp
        let env1 = newBlock env
        case checkStm env1 typ stm1 of
            Ok env -> do
                let (sig, _:cxts) = env
                let env2 = newBlock (sig, cxts)
                case checkStm env2 typ stm2 of
                    Ok env -> do
                        let (sig1, _:cxts1) = env
                        return (sig1, cxts1)
                    Bad string -> Bad string
            Bad string -> Bad string
    SWhile exp stm1 -> do
        checkExp env Bool exp
        let env1 = newBlock env
        case checkStm env1 typ stm1 of
            Ok env -> do
                let (sig, _:cxts) = env
                return (sig, cxts)
            Bad string -> Bad string
    SExp exp -> do
        inferExp env exp
        return env

addItem :: Env -> Type -> Item -> Err Env
addItem env typ (NoInit id) = do
    updateVar env id typ 
addItem env typ (Init id exp) = do
    etyp <- inferExp env exp
    if typ == etyp then updateVar env id typ
    else fail "mismatch operand types"

-- Inference functions
inferExp :: Env -> Exp -> Err Type
inferExp env ex = case ex of
    EId id      -> lookupVar env id
    EInt _      -> Ok Int
    EDouble _   -> Ok Double
    ETrue       -> Ok Bool
    EFalse      -> Ok Bool
    EApp id exps -> inferApp env id exps
    EString _   -> Ok Int
    ENeg exp    -> inferNeg env exp
    ENot exp    -> inferNot env exp
    EMul exp1 _ exp2    -> inferBin env exp1 exp2
    EAdd exp1 _ exp2    -> inferBin env exp1 exp2
    ECmp exp1 OLt exp2      -> inferCmp env exp1 exp2
    ECmp exp1 OLtEq exp2    -> inferCmp env exp1 exp2
    ECmp exp1 OGt exp2      -> inferCmp env exp1 exp2
    ECmp exp1 OGtEq exp2    -> inferCmp env exp1 exp2
    ECmp exp1 OEq exp2      -> inferEq env exp1 exp2
    ECmp exp1 ONEq exp2     -> inferEq env exp1 exp2
    EAnd exp1 exp2          -> inferLogic env exp1 exp2
    EOr  exp1 exp2          -> inferLogic env exp1 exp2

inferNeg :: Env -> Exp -> Err Type
inferNeg env exp = case inferExp env exp of
    Ok Int -> Ok Int
    Ok Double -> Ok Double
    _ -> Bad "Non-number variables cannot be negative"

inferNot :: Env -> Exp -> Err Type
inferNot env exp = case inferExp env exp of
    Ok Bool -> Ok Bool
    _ -> Bad "Non-boolean variables do not have a 'not' value associated to them"

inferBin :: Env -> Exp -> Exp -> Err Type
inferBin env exp1 exp2 = do
    typ <- inferExp env exp1
    case typ of
        Double -> do
            typ2 <- inferExp env exp2
            case typ2 of
                Int    -> Ok Double
                Double -> Ok Double
                _           -> Bad "inferBin: can only use arithmetic binary operators on numbers"
        Int -> do
            typ2 <- inferExp env exp2
            case typ2 of
                Int    -> Ok Int
                Double -> Ok Double
                _           -> Bad "inferBin: can only use arithmetic binary operators on numbers"
        _ -> Bad $ "wrong type of expression" ++ printTree exp1

inferCmp :: Env -> Exp -> Exp -> Err Type
inferCmp env exp1 exp2 = do
    if inferExp env exp1 `elem` [Ok Int, Ok Double] then do
        if inferExp env exp2 `elem` [Ok Int, Ok Double] then 
            Ok Bool
        else
            Bad "inferCmp: Can only compare numbers"
    else
        Bad "inferCmp: Can only compare numbers"

inferEq :: Env -> Exp -> Exp -> Err Type
inferEq env exp1 exp2 = do
    case inferExp env exp1 of
        Ok Bool -> do
            case inferExp env exp2 of
                Ok Bool -> Ok Bool
                Ok _ -> Bad "inferEq: Cannot check equality of boolean and non-boolean"
        Ok Int -> do
            if inferExp env exp2 `elem` [Ok Int, Ok Double] then
                Ok Bool
            else Bad "inferEq: Cannot check equality of different types"
        Ok Double -> do
            if inferExp env exp2 `elem` [Ok Int, Ok Double] then
                Ok Bool
            else Bad "inferEq: Cannot check equality of different types"
        _ -> Bad "inferEq: Can only check equality of int, double and bool"

inferIncDec :: [Type] -> Env -> Ident -> Err Type
inferIncDec types env id = do
    typ <- lookupVar env id
    if typ `elem` types then
        Ok typ
    else
        Bad "Increment/Decrement can only be applied to Ints and Doubles"

inferLogic :: Env -> Exp -> Exp -> Err Type
inferLogic env exp1 exp2 = do
    typ <- inferExp env exp1
    if typ == Bool then do
        checkExp env typ exp2
    else
        Bad "inferLogic: type is not bool"

inferApp :: Env -> Ident -> [Exp] -> Err Type
inferApp env id exps = case lookupFun env id of
    Ok (argTypes, returnType) -> case checkFunTypes env argTypes exps of
        Ok _ -> Ok returnType
        Bad str -> Bad str
    Bad s -> Bad s

checkFunTypes :: Env -> [Type] -> [Exp] -> Err ()
checkFunTypes _ [] [] = Ok ()
checkFunTypes env (typ:typs) (exp:exps) = case checkAssExp env typ exp of
    Ok _ -> checkFunTypes env typs exps
    Bad str -> Bad str
checkFunTypes _ _ _ = Bad "checkFunTypes: different lengths in arguments"