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
type Sig = Map Id ([Type],Type) -- function type signature dictionary and return type
type Context = Map Id Type      -- variables with their types


typecheck :: Program -> Err Program
typecheck (PDefs defs) = do 
    env <- initSymbolTable $ Env Map.empty [Map.empty]
    env <- createSymbolTable env defs
    case lookupDef env (Id "main") of 
        Ok ([], Int) -> do
                (env',defs') <- checkDefs env defs -- inplace foldM_?
                return (PDefs defs')
        _ -> Bad "main() method does not exist"

initSymbolTable :: Env -> Err Env
initSymbolTable env = do 
    env <- updateFun env (Id "printInt")    ([Int], Type_void)
    env <- updateFun env (Id "printDouble") ([Double], Type_void)
    env <- updateFun env (Id "readInt")     ([], Int)
    updateFun env (Id "readDouble")  ([], Double)

createSymbolTable :: Env -> [Def] -> Err Env
createSymbolTable env [] = return env
createSymbolTable env ((DFun retType i args stms):ds) = do
    env' <- updateFun env i (map getArgType args, retType)
    createSymbolTable env' ds
    where 
        getArgType (ADecl t i) = t

checkEqualTypes :: Env -> [Type] -> [Exp] -> (Bool,[Exp])
checkEqualTypes env [] [] = (True, [])
checkEqualTypes env (t:_) [] = (False, [])
checkEqualTypes env [] (e:_) = (False, [])
checkEqualTypes env (t:ts) (e:es) = do
    case checkExpType env e of
        Ok (et',e') -> do
            let (b,aexps) = checkEqualTypes env ts es
            (b,typecast et' t e': aexps)
        _ -> (False,[])
    where 
        typecast t1 t2 ex = if t1 /= t2 then EI2D ex else ex

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
    if t1 /= t' then return (t',(EI2D e1', e2'))
    else if t2 /= t' then return (t',(e1',EI2D e2'))
    else return (t',(e1',e2'))

updateFun :: Env -> Id -> ([Type],Type) -> Err Env
updateFun (Env sigDict ctxDict) i s = do
    if Map.member i sigDict
        then fail "Function is already defined"
        else return $ Env (Map.insert i s sigDict) ctxDict

lookupDef :: Env -> Id -> Err([Type],Type) -- aka lookupFun
lookupDef (Env sigDict ctxDict) id = case Map.lookup id sigDict of
                                            Just val -> return val
                                            Nothing -> fail "Unknown function"

lookupVar :: Env -> Id -> Err Type
lookupVar (Env sigDict []) id = fail "Unknown variable"
lookupVar (Env sigDict (c:ctxDict)) id = case Map.lookup id c of
                                            Just retType -> return retType
                                            Nothing -> lookupVar (Env sigDict ctxDict) id

addVar :: Type -> Id -> Env -> Err Env -- aka updateVar
addVar t i (Env s (c:cs)) = do
    case t of
        Type_void -> fail "Cannot declare void variable"
        _ -> if Map.member i c
                then fail "Variable already declared"
                else return $ Env s (Map.insert i t c : cs)

validCmp :: CmpOp -> Type -> Err Type
validCmp _ Type_void = fail "Cannot compare void"
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
checkStm _ _ (SDecls Type_void _) = fail "Void var not allowed"
checkStm _ env (SDecls t ids) = do 
    env' <- foldM (addVarFold t) env ids 
    return (env', SDecls t ids)
    where addVarFold ty env id = addVar ty id env
checkStm _ env (SInit typ items) = do

checkStm _ env (SAss id exp) = do
    t1 <- lookupVar env id
    (t2,e2') <- checkExpType env exp
    t' <- checkAssEqualType t1 t2
    if t' == t2
        then return (t1, Init id e2')
        else return (t1, Init id (EI2D e2'))
{-
checkStm _ env (SInit t id e) = do
    env' <- addVar t id env
    (t', e') <- checkExpType env' e -- Exp type
    t'' <- checkEqualType t t' -- Typecasted type
    if t''  ==  t'
        then
            return (env', SInit t id e')
        else do
            return (env', SInit t id (EI2D e')) -- Type and exp same type, id not taken
-}
checkStm _ env (SExp e) = do
    (t',e') <- checkExpType env e
    return (env, SExp t' e')
checkStm r env (SReturn e) = do
    (t1,e') <- checkExpType env e
    t' <- checkAssEqualType r t1
    if t' /= t1 then Ok (env,SReturn t' (EI2D e')) 
    else Ok (env, SReturn t' e')
checkStm r env (SBlock ss) = do
    (env',ss') <- checkStms r (enterScope env) ss -- fold checkStm check if fail
    env'' <- leaveScope (Ok env')
    return (env'', SBlock ss')
checkStm r env (SWhile e s) = do
    (t, e') <- checkExpType env e
    if t == Type_bool 
        then do
            (env',s') <- checkStm r (enterScope env) s
            env'' <- leaveScope (Ok env')
            return (env'', SWhile e' s')
        else fail "invalid exp type in while statement"-- e is bool, s is not fail
checkStm r env (SIfElse e ifs elses) = do
    (t',e') <- checkExpType env e
    if t' == Type_bool 
        then do
            (env',ifs') <- checkStm r (enterScope env) ifs 
            env'' <- leaveScope $ Ok env'
            (env''',elses') <- checkStm r (enterScope env'') elses
            env'''' <- leaveScope (Ok env''')
            return (env'''', SIfElse e' ifs' elses')
        else fail "invalid exp type"-- e is bool, checkStm ifs, checkStm elses
checkStm r env (SIncr id) = do
    case lookupVar env id of
        Ok Int -> return (Int, SIncr id)
        Ok Double -> return (Double, SIncr id)
        _ -> fail "non numeric type" 
checkStm r env (SDecr id) = do
    case lookupVar env id of
        Ok Int -> return (Int, SDecr id)
        Ok Double -> return (Double, SDecr id)
        _ -> fail "non numeric type" 

addItem :: Env -> Type -> Item -> Err Env
addItem env typ (NoInit id) = do
    env' <- addVar typ id env
    return env'
addItem env (Init id exp) = do
    t1 <- lookupVar env id
    (t2,e2') <- checkExpType env exp
    t' <- checkAssEqualType t1 t2
    if t' == t2
        then return (t1, Init id e2')
        else return (t1, Init id (EI2D e2'))


checkExpType :: Env -> Exp -> Err (Type, Exp)
checkExpType env (EInt e) = return (Int, EInt e)
checkExpType env (EBool LTrue) = return (Type_bool, EBool True)
checkExpType env (EBool LFalse) = return (Type_bool, EBool False)
checkExpType env (EDouble e) = return (Double, EDouble e)
checkExpType env (EId id) = do
    t <- lookupVar env id
    return (t, EId id)
checkExpType env (EApp id exps) = do 
    (argTypes, retType) <- lookupDef env id
    let (b,exps') = checkEqualTypes env argTypes exps
    if b -- Check if valid type casting (int <-> double)
        then return (retType, EApp id exps')
        else fail "invalid argtypes"
checkExpType env (EMul e1 OTimes e2) = do
    case checkOprtype e1 e2 env of
        Ok (Int,(e1',e2')) -> return (Int, EArith Int e1' OTimes e2')
        Ok (Double,(e1',e2')) -> return (Double, EArith Double e1' OTimes e2')
        _ -> fail "non numeric type"
checkExpType env (EMul e1 ODiv e2) = do
    case checkOprtype e1 e2 env of
        Ok (Int,(e1',e2')) -> return (Int, EArith Int e1' ODiv e2')
        Ok (Double,(e1',e2')) -> return (Double, EArith Double e1' ODiv e2')
        _ -> fail "non numeric type"
checkExpType env (EAdd e1 OPlus e2) = do
    case checkOprtype e1 e2 env of
        Ok (Int,(e1',e2')) -> return (Int, EArith Int e1' OPlus e2')
        Ok (Double,(e1',e2')) -> return (Double, EArith Double e1' OPlus e2')
        _ -> fail "non numeric type"
checkExpType env (EAdd e1 OMinus e2) = do
    case checkOprtype e1 e2 env of
        Ok (Int,(e1',e2')) -> return (Int, EArith Int e1' OMinus e2')
        Ok (Double,(e1',e2')) -> return (Double, EArith Double e1' OMinus e2')
        _ -> fail "non numeric type"
checkExpType env (ECmp e1 op e2) = do 
    (t',(e1',e2')) <- checkOprtype e1 e2 env -- t' is typecasted
    t'' <- validCmp op t' 
    return (Type_bool,ECmp t'' e1' op e2')
checkExpType env (EAnd e1 e2) = do
    (t', (e1',e2')) <- checkOprtype e1 e2 env
    if t' == Type_bool then return (Type_bool, EAnd e1' e2') else fail "Bool required for And operator"
checkExpType env (EOr e1 e2) = do
    (t', (e1',e2')) <- checkOprtype e1 e2 env
    if t' == Type_bool then return (Type_bool, EOr e1' e2') else fail "Bool required for Or operator"
--checkExpType env (Init id exp) = do
--    t1 <- lookupVar env id
--    (t2,e2') <- checkExpType env exp
--    t' <- checkAssEqualType t1 t2
--    if t' == t2
--        then return (t1, Init id e2')
--        else return (t1, Init id (EI2D e2'))

enterScope :: Env -> Env
enterScope (Env sig cs) = Env sig (Map.empty:cs)

leaveScope :: Err Env -> Err Env
leaveScope (Ok (Env s (c:cs))) = return (Env s cs)
leaveScope e = e