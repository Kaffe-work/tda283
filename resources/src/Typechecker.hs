module TypeChecker where

import Control.Applicative
import Control.Monad
import Control.Monad.Except ()
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Javalette.Abs

import Javalette.Print (printTree)

import Javalette.ErrM

-- | Entry point of type checker.
data Env = Env {sig :: Sig, context :: [Context]} -- functions and context stack
type Sig = Map Ident ([Type],Type) -- function type signature dictionary and return type
type Context = Map Ident Type      -- variables with their types


typecheck :: Program -> Err Program
typecheck (Pdefs defs) = do 
    env <- initSymbolTable $ Env Map.empty [Map.empty]
    env <- createSymbolTable env defs
    case lookupDef env (Ident "main") of 
        Ok ([], Int) -> do
                (env',defs') <- checkDefs env defs -- inplace foldM_?
                return (Pdefs defs')
        _ -> Bad "main() method does not exist"

initSymbolTable :: Env -> Err Env
initSymbolTable env = do 
    env <- updateFun env (Ident "printInt")    ([Int], Void)
    env <- updateFun env (Ident "printDouble") ([Double], Void)
    env <- updateFun env (Ident "readInt")     ([], Int)
    env <- updateFun env (Ident "printString") ([Int], Void)
    updateFun env (Ident "readDouble")  ([], Double)

createSymbolTable :: Env -> [Def] -> Err Env
createSymbolTable env [] = return env
createSymbolTable env ((DFun retType i args stms):ds) = do
    env' <- updateFun env i (map getArgType args, retType)
    createSymbolTable env' ds
    where 
        getArgType (ADecl t i) = t

checkEqualTypes :: Env -> [Type] -> [Exp] -> Err (Bool,[Exp])
checkEqualTypes env [] [] = Ok (True, [])
checkEqualTypes env (t:_) [] = Ok (False, [])
checkEqualTypes env [] (e:_) = Ok (False, [])
checkEqualTypes env (typ:typs) (exp:exps) = do
    case checkExpType env exp of
        Ok (exptyp,exp2) -> do
            case checkEqualTypes env typs exps of
                Ok (b, aexps) -> do
                    case typecast exptyp typ exp2 of
                        Ok exp -> Ok (b, exp:aexps)
                        _ -> fail "Not equal types"
                Bad str -> fail str
        _ -> Ok (False,[])
    where 
        typecast t1 t2 ex = if t1 /= t2 then fail "Type bad" else Ok ex

-- Double and int, are interchangeable
checkEqualType :: Type -> Type -> Err Type
checkEqualType t1 t2 = if t1 == t2 
    then return t1
    else do
        case (t1,t2) of
            (Double, Int) -> return Double
            (Int, Double) -> return Double
            _ -> fail "Mismatch in operand types" 

-- Special case for assignment where the bigger type only goes one way
-- Note: biger type first (double)
checkAssEqualType :: Type -> Type -> Err Type
checkAssEqualType t1 t2 = if t1 == t2 
    then return t1
    else do
        case (t1,t2) of
            (Double, Int) -> return Double
            _ -> fail "Mismatch in operand types" 

-- big small
checkOprtype :: Exp -> Exp -> Env -> Err (Type,(Exp,Exp))
checkOprtype  e1 e2 env = do
    (t1,e1') <- checkExpType env e1
    (t2,e2') <- checkExpType env e2
    t' <- checkEqualType t1 t2
    if t1 /= t' then fail "Mismatch in operand types 1" 
    else if t2 /= t' then fail "Mismatch in operand types for 2" 
    else return (t',(e1',e2'))

updateFun :: Env -> Ident -> ([Type],Type) -> Err Env
updateFun (Env sigDict ctxDict) i s = do
    if Map.member i sigDict
        then fail "Function is already defined"
        else return $ Env (Map.insert i s sigDict) ctxDict

lookupDef :: Env -> Ident -> Err([Type],Type) -- aka lookupFun
lookupDef (Env sigDict ctxDict) id = case Map.lookup id sigDict of
                                            Just val -> return val
                                            Nothing -> fail ("unknown function " ++ show id)

lookupVar :: Env -> Ident -> Err Type
lookupVar (Env sigDict []) id = fail "Unknown variable"
lookupVar (Env sigDict (c:ctxDict)) id = case Map.lookup id c of
                                            Just retType -> return retType
                                            Nothing -> lookupVar (Env sigDict ctxDict) id

addVar :: Type -> Ident -> Env -> Err Env -- aka updateVar
addVar typ id (Env s (c:cs)) = do
    case typ of
        Void -> fail "Cannot declare void variable"
        _ -> if Map.member id c
                then fail "Variable already declared"
                else return $ Env s (Map.insert id typ c : cs)

validCmp :: CmpOp -> Type -> Err Type
validCmp _ Void = fail "Cannot compare void"
validCmp OEq t  = return t
validCmp ONEq t = return t
validCmp _ t = do
    case t of
        Int -> Ok t
        Double -> Ok t
        _ -> fail "Unable to compare types"

checkDefs :: Env -> [Def] -> Err (Env, [Def])
checkDefs e [] = return (e,[])
checkDefs env (d:ds) = do
    (e',d') <- checkDef env d
    (e'',d'') <- checkDefs e' ds
    return (e'',d':d'')

checkDef :: Env -> Def -> Err (Env, Def)
checkDef env (DFun retType i args stms) = do
    env <- foldM addArg (enterScope env) args
    (env', stms') <- checkStms retType env stms 
    env'' <- leaveScope (Ok env')
    return (env'', DFun retType i args stms')
    where
        addArg env (ADecl t i) = addVar t i env

checkStms :: Type -> Env -> [Stm] -> Err (Env, [Stm])
checkStms t e [] = return (e, [])
checkStms t env (s:ss) = do
    (env', s') <- checkStm t env s
    (env'', ss') <- checkStms t env' ss
    return (env'', s':ss')

checkStm :: Type -> Env -> Stm -> Err (Env,Stm)
checkStm _ env SEmpty = Ok (env, SEmpty)

checkStm r env (SBlock ss) = do
    (env',ss') <- checkStms r (enterScope env) ss -- fold checkStm check if fail
    env'' <- leaveScope (Ok env')
    return (env'', SBlock ss')
    
checkStm _ _ (SDecls Void _) = fail "Void var not allowed"
checkStm _ env (SDecls typ items) = do 
    env2 <- foldM (addItemFold typ) env items 
    return (env2, SDecls typ items)
    where addItemFold typ env item = addItem env typ item
    
checkStm _ env (SAss id exp) = do
    t1 <- lookupVar env id
    (t2,e2') <- checkExpType env exp
    t' <- checkAssEqualType t1 t2
    if t' == t2
        then return (env, SAss id e2')
        else fail "mismatch operand types"

checkStm r env (SIncr id) = do
    case lookupVar env id of
        Ok Int -> return (env, SIncr id)
        Ok Double -> return (env, SIncr id)
        _ -> fail "non numeric type" 

checkStm r env (SDecr id) = do
    case lookupVar env id of
        Ok Int -> return (env, SDecr id)
        Ok Double -> return (env, SDecr id)
        _ -> fail "non numeric type" 

checkStm r env (SReturn e) = do
    (t1,e') <- checkExpType env e
    t' <- checkAssEqualType r t1
    if t' /= t1 then fail "wrong operands" 
    else Ok (env, SReturn e')

checkStm styp env SNoReturn = Ok (env, SNoReturn)

checkstm r env (SIf e ifs) = do
    (t',e') <- checkExpType env e
    if t' == bool
        then do
            --todo
        else fail "invalid expression type in if statement"

checkStm r env (SIfElse e ifs elses) = do
    (t',e') <- checkExpType env e
    if t' == Bool 
        then do
            (env',ifs') <- checkStm r (enterScope env) ifs 
            env'' <- leaveScope $ Ok env'
            (env''',elses') <- checkStm r (enterScope env'') elses
            env'''' <- leaveScope (Ok env''')
            return (env'''', SIfElse e' ifs' elses')
        else fail "invalid exp type in if else"-- e is bool, checkStm ifs, checkStm elses

checkStm r env (SWhile e s) = do
    (t, e') <- checkExpType env e
    if t == Bool 
        then do
            (env',s') <- checkStm r (enterScope env) s
            env'' <- leaveScope (Ok env')
            return (env'', SWhile e' s')
        else fail "invalid exp type in while statement"-- e is bool, s is not fail

checkStm _ env (SExp e) = do
    (t',e') <- checkExpType env e
    return (env, SExp  e')


addItem :: Env -> Type -> Item -> Err Env
addItem env typ (NoInit id) = do
    addVar typ id env
addItem env typ (Init id exp) = do
    (etyp, exp2) <- checkExpType env exp
    if typ == etyp then addVar typ id env
    else fail "mismatch operand types"


checkExpType :: Env -> Exp -> Err (Type, Exp)
checkExpType env (EId id) = do
    t <- lookupVar env id
    return (t, EId id)

checkExpType env (EInt e) = return (Int, EInt e)

checkExpType env (EDouble e) = return (Double, EDouble e)

checkExpType env ETrue = return (Bool, ETrue)

checkExpType env EFalse = return (Bool, EFalse)

checkExpType env (EApp id exps) = do 
    (argTypes, retType) <- lookupDef env id
    case checkEqualTypes env argTypes exps of
        Ok (b, exps2) -> do
            if b -- Check if valid type casting (int <-> double)
                then return (retType, EApp id exps2)
                else fail $ "invalid argtypes " ++ show id
        Bad str -> Bad str

checkExpType env (EString str) = do
    return (Int, EString str)
    
checkExpType env (ENeg exp) = do
    case checkExpType env exp of
        Ok (Int, exp2)      -> Ok (Int, ENeg exp2)
        Ok (Double, exp2)   -> Ok (Double, ENeg exp2)
        Bad _               -> fail "Cannot neg a non-number type"

checkExpType env (ENot exp) = do
    case checkExpType env exp of
        Ok (Bool, exp2) -> Ok (Bool, ENot exp2)
        Bad _           -> fail "Cannot 'not' a non-boolean"
        
checkExpType env (EMul e1 OTimes e2) = do
    case checkOprtype e1 e2 env of
        Ok (Int,(e1',e2')) -> return (Int, EMul e1' OTimes e2')
        Ok (Double,(e1',e2')) -> return (Double, EMul e1' OTimes e2')
        _ -> fail "non numeric type"
checkExpType env (EMul e1 ODiv e2) = do
    case checkOprtype e1 e2 env of
        Ok (Int,(e1',e2')) -> return (Int, EMul e1' ODiv e2')
        Ok (Double,(e1',e2')) -> return (Double, EMul  e1' ODiv e2')
        _ -> fail "non numeric type"
checkExpType env (EMul e1 OMod e2) = do
    case checkOprtype e1 e2 env of
        Ok (Int,(e1',e2')) -> return (Int, EMul e1' OMod e2')
        Ok (Double,(e1',e2')) -> return (Double, EMul  e1' OMod e2')
        _ -> fail "non numeric type"
        
checkExpType env (EAdd e1 OPlus e2) = do
    case checkOprtype e1 e2 env of
        Ok (Int,(e1',e2')) -> return (Int, EAdd  e1' OPlus e2')
        Ok (Double,(e1',e2')) -> return (Double, EAdd  e1' OPlus e2')
        _ -> fail "non numeric type"
checkExpType env (EAdd e1 OMinus e2) = do
    case checkOprtype e1 e2 env of
        Ok (Int,(e1',e2')) -> return (Int, EAdd e1' OMinus e2')
        Ok (Double,(e1',e2')) -> return (Double, EAdd e1' OMinus e2')
        _ -> fail "non numeric type"
        
checkExpType env (ECmp e1 op e2) = do 
    (t',(e1',e2')) <- checkOprtype e1 e2 env -- t' is typecasted
    t'' <- validCmp op t' 
    return (Bool, ECmp e1' op e2')

checkExpType env (EAnd e1 e2) = do
    (t', (e1',e2')) <- checkOprtype e1 e2 env
    if t' == Bool then return (Bool, EAnd e1' e2') else fail "Bool required for And operator"

checkExpType env (EOr e1 e2) = do
    (t', (e1',e2')) <- checkOprtype e1 e2 env
    if t' == Bool then return (Bool, EOr e1' e2') else fail "Bool required for Or operator"

enterScope :: Env -> Env
enterScope (Env sig cs) = Env sig (Map.empty:cs)

leaveScope :: Err Env -> Err Env
leaveScope (Ok (Env s (c:cs))) = return (Env s cs)
leaveScope e = e