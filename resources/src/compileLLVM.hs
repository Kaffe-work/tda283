{-# OPTIONS_GHC -Wunused-top-binds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Compiler for C--, producing symbolic JVM assembler.

module Compiler where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.RWS

import Data.Maybe ( fromMaybe )
import Data.Map (Map)
import qualified Data.Map as Map

import Javalette.Abs
import LLVM
    ( negateCmp,
      Code(..),
      Fun(..),
      Addr,
      FunType(FunType),
      Label(L),
      Size(..),
      ToLLVM(tollvm) )

pattern IfZ l = If OEq l
pattern IfNZ l = If ONEq l

type Sig = Map Ident Fun

type Cxts = [Block]
type Block = [(Ident, Type)]

data St = St {
    sig :: Sig,
    cxts :: Cxts,
    limitLocals :: Int,
    currentStack :: Int,
    limitStack :: Int,
    nextLabel :: Label,
    output :: Output
}

initSt :: Sig -> St
initSt s = St {
    sig = s,
    cxts = [[]],
    limitLocals = 0,
    currentStack = 0,
    limitStack = 0,
    nextLabel = L 0,
    output = []
}

addBuiltInFun :: Sig -> Sig
addBuiltInFun = Map.union (Map.fromList builtin)

type Output = [Code]

type Compile = State St

-- | Entry point.

compile
  :: String  -- ^ Class name.
  -> Program -- ^ Type-annotated program.
  -> String  -- ^ Generated jasmin source file content.
compile name (PDefs defs) = do
    unlines $ concat $ header : map (compileDef initSig) defs
    where
        initSig = Map.fromList $ builtin ++ map sigEntry defs
        sigEntry def@(DFun _ id@(Id id1) _ _) = (id, Fun (Id $name ++ "/" ++ id1) $ funType def)
        header = concat
          [  [ ";; BEGIN HEADER"
            , ""
            , ".class public " ++ name
            , ".super java/lang/Object"
            , ""
            , ".method public <init>()V"
            , "  .limit locals 1"
            , ""
            ],
            map indent
            [ "  aload_0"
            , "  invokespecial java/lang/Object/<init>()V"
            , "  return"
            ]
            , [""
            , ".end method"
            , ""
            , ".method public static main([Ljava/lang/String;)V"
            , "  .limit locals 1"
            , "  .limit stack  1"
            , ""
            ],
            map indent
            [ "  invokestatic " ++ name ++ "/main()I"
            , "  pop"
            , "  return"
            ]
            , [""
            , ".end method"
            , ""
            , ";; END HEADER"
            ]
          ]

builtin :: [(Ident, Fun)]
builtin =
    [ (Id "printInt", Fun (Id "Runtime/printInt") $ FunType Void [Int]),
      (Id "readInt", Fun (Id "Runtime/readInt") $ FunType Int []),
      (Id "printDouble", Fun (Id "Runtime/printDouble") $ FunType Void [Double]),
      (Id "readDouble", Fun (Id "Runtime/readDouble") $ FunType Double []),
      (Id "printString", Fun (Id "Runtime/printString") $ FunType Void [Int])]


indent :: String -> String
indent s = if null s then s else "\t" ++ s

compileDef :: Sig -> Def -> [String]
compileDef sig0 def@(DFun typ id args stms) = concat
    [["",
      ".define " ++ ToLLVM (Fun id $ funType def)
    ],
    [".limit locals " ++ show (limitLocals st),
     ".limit stack " ++ show (limitStack st)
    ],
    map (indent . ToLLVM) $ reverse (output st),
    ["ret",
     ".end method"
    ]
    ]
    where
    st = execState (compileFun typ def) $ initSt sig0

compileFun :: Type -> Def -> Compile ()
compileFun t (DFun typ id args stms) = do
    mapM_ (\ (ADecl t' id') -> newVar id' t') args
    mapM_ compileStm stms

compileStm :: Stm -> Compile ()
compileStm stm = do
    {-
    let top = stmTop s0
    unless (null top) $ do
        blank
        mapM_ comment $ lines top
    -}
    case stm of
        SExp typ exp -> do
            compileExp exp
            emit $ Pop typ
        SDecls typ ids -> do
            mapM_ (`newVar` typ) ids
        Init typ id exp -> do
            newVar id typ
            compileExp exp
            (addr, _) <- lookupVar id
            emit $ Store typ addr
        NoInit typ ids -> do
            
        SReturn typ exp -> do
            compileExp exp
            emit $ Return typ
        SWhile exp stm -> do
            true <- newLabel
            false <- newLabel
            emit $ Label true
            compileExp exp
            newBlock (do
                emit $ If OEq false
                compileStm stm)
            emit $ Goto true
            emit $ Label false
        SBlock stms -> newBlock (mapM_ compileStm stms)
        SIfElse exp stm1 stm2 -> do
            true <- newLabel
            false <- newLabel
            compileExp exp
            emit $ If OEq false
            newBlock (compileStm stm1)
            emit $ Goto true
            emit $ Label false
            newBlock (compileStm stm2)
            emit $ Label true

{-
compileCond :: Bool -> Label -> Exp -> Compile ()
compileCond cond l exp = case exp of
    EBool LTrue -> when cond $ emit $ Goto l
    EBool LFalse -> unless cond $ emit $ Goto l
    ECmp t e1 op e2 -> do
        compileExp e1
        compileExp e2
        emit $ IfCmp t (if cond then op else negateCmp op) l
    e -> do
        compileExp e
        emit $ (if cond then IfNZ else IfZ) l
        -}

compileExp :: Exp -> Compile ()
compileExp exp = case exp of
    EBool LTrue -> emit $ IConst 1
    EBool LFalse -> emit $ IConst 0
    EInt i -> emit $ IConst i
    EDouble d -> emit $ DConst d
    EId id -> do
        (addr, typ) <- lookupVar id
        emit $ Load typ addr
    EApp id exps-> do
        fun <- fromMaybe (error $ "Undefined " ++ show id {-++ printTree f-}) . Map.lookup id <$> gets sig
        -- error $ "fun: " ++ show fun ++ " exps: " ++ show exps
        mapM_ compileExp exps
        emit $ Call fun
    EPost typ id OInc -> compilePost typ id OPlus
    EPost typ id ODec -> compilePost typ id OMinus
    EPre typ OInc id -> compilePre typ id OPlus
    EPre typ ODec id -> compilePre typ id OMinus
    EMul typ exp1 op exp2 -> do
        compileExp exp1
        compileExp exp2
        emit $ Mult typ op
    EAdd typ exp1 op exp2 -> do
        compileExp exp1
        compileExp exp2
        emit $ Add typ op
    ECmp typ exp1 cmpOp exp2 -> compileCmp typ exp1 exp2 cmpOp
    EAnd exp1 exp2 -> do
        compileExp exp1
        true <- newLabel
        false <- newLabel
        emit $ If OEq false -- check exp1
        compileExp exp2 -- exp1 true
        emit $ Goto true
        emit $ Label false
        emit $ IConst 0
        emit $ Label true
    EOr exp1 exp2 -> do
        compileExp exp1
        true <- newLabel
        false <- newLabel
        emit $ If OEq false -- check exp1
        emit $ IConst 1 -- exp1 true
        emit $ Goto true
        emit $ Label false
        compileExp exp2 -- check if exp2 is true
        emit $ Label true
    EAss id exp -> do
        (addr, typ) <- lookupVar id
        compileExp exp
        emit $ Store typ addr
        emit $ Load typ addr

compilePost :: Type -> Id -> AddOp -> Compile ()
compilePost typ id op = do
    (addr, typ) <- lookupVar id
    emit $ Load typ addr
    emit $ Dup typ
    case typ of
        Int -> emit $ IConst 1
        Double -> emit $ DConst 1
    emit $ Add typ op
    emit $ Store typ addr -- Postinc does not eval to the updated val

compilePre :: Type -> Id -> AddOp -> Compile ()
compilePre typ id op = do
    (addr, typ) <- lookupVar id
    emit $ Load typ addr
    emit $ Dup typ
    case typ of
        Int -> emit $ IConst 1
        Double -> emit $ DConst 1
    emit $ Add typ op
    emit $ Store typ addr
    case typ of
        Int -> emit $ IConst 1
        Double -> emit $ DConst 1
    emit $ Add typ op -- Probably should use Inc, but address is a problem

compileCmp :: Type -> Exp -> Exp -> CmpOp -> Compile ()
compileCmp typ exp1 exp2 op = do
    compileExp exp1
    compileExp exp2
    true <- newLabel
    false <- newLabel
    emit $ IfCmp typ op true
    emit $ IConst 0 -- cmp evaled to false
    emit $ Goto false
    emit $ Label true
    emit $ IConst 1
    emit $ Label false

newLabel :: Compile Label
newLabel = do
    l <- gets nextLabel
    modify $ \ st -> st {nextLabel = succ l}
    return l

newBlock :: Compile a -> Compile a
newBlock cxt = do
    modify $ \ st -> st {cxts = []: cxts st}
    a <- cxt
    modify $ \ st -> st {cxts = tail $ cxts st}
    return a

exitBlock :: Compile ()
exitBlock = do
    cs <- gets cxts
    case cs of
        (c:cs') -> modify $ \ st -> st {cxts = cs'}
        [] -> error "exitBlock: Cannot exit topmost block"

{-
newVar :: Id -> Type -> Compile ()
newVar id typ = do
    limLocls <- gets limitLocals
    cxts <- gets cxt
    case cxts of
        (c:cs) -> do
            case typ of
                Double -> modify $ \ st -> st {cxt = Map.insert id (limLocls, Double) c:cs, limitLocals = limLocls + 2 }
                _ -> modify $ \ st -> st {cxt = Map.insert id (limLocls, typ) c:cs, limitLocals = limLocls + 1 }
        [] -> error "newVar: no context"
-}

newVar :: Ident -> Type -> Compile ()
newVar id typ = do
    modify $ \ st@St{ cxts = (b:bs) } -> st { cxts = ((id,typ) : b) : bs }
    updateLimitLocals

lookupVar :: Ident -> Compile (Addr, Type)
lookupVar id = gets ((loop . concat) . cxts)
    where
        loop [] = do
            error $ "Variable " ++ show id ++ " is unbound"
        loop ((id1, typ) : cs)
          | id == id1 = (size cs, typ)
          | otherwise = loop cs

updateLimitLocals :: Compile ()
updateLimitLocals = do
  old <- gets limitLocals
  new <- gets (size . cxts)
  when (new > old) $
    modify $ \ st -> st { limitLocals = new }


incStack :: Size t => t -> Compile ()
incStack t = modStack (size t)

decStack :: Size t => t -> Compile ()
decStack t = modStack $ negate (size t)

modStack :: Int -> Compile ()
modStack n = do
    new <- gets ((n +) . currentStack)
    modify $ \ st -> st {currentStack = new}
    old <- gets limitStack
    when (new > old) $
        modify $ \ st -> st {limitStack = new}

emit :: Code -> Compile ()
emit (Store Void _) = return ()
emit (Load Void _) = return ()
emit (Dup Void) = return ()
emit (Pop Void) = return ()
emit (Inc typ@Double addr d) = do
    emit $ Load typ addr
    emit $ DConst $ fromIntegral d
    emit $ Add typ OPlus
    emit $ Store typ addr
emit (IfCmp Double op l) = do -- for comparision with doubles
    emit $ DCmp
    emit $ If op l
emit c = do
    modify $ \ st@St{output = cs} -> st {output = c:cs}
    adjustStack c

    {--
adjustStack :: Code -> Compile ()
adjustStack c = case c of
    Alloca t
    Store t _
    Load  t 
    Call Type Addr [(Type, Addr)]
    Label Label
    Ret Type
    Branch Label
    Cmp Type CmpOp
    Add Type AddOp
    Mul Type MulOp
    Neg Type
    Not Type


    Store t _ -> decStack t
    Load t _ -> incStack t
    IConst _ -> incStack Int
    DConst _ -> incStack Double
    Dup t -> incStack t
    Pop t -> decStack t
    Return t -> decStack t
    Call f -> decStack f
    Label{} -> return ()
    Goto{} -> return ()
    If _ _ -> decStack Int
    IfCmp t _ _ -> decStack t >> decStack t
    DCmp -> decStack Double >> decStack Double >> incStack Int
    Inc{} -> return ()
    Add t _ -> decStack t
    Mult t _ -> decStack t
    I2D -> decStack Int >> incStack Double
    Comment _ -> return ()
    --}

comment :: String -> Compile ()
comment =  emit . Comment

blank :: Compile ()
blank = comment ""

{-
stmTop :: Stm -> String
stmTop stm = case stm of
    SWhile e _ -> "while (" ++ printTree e ++ ")"
    SIfElse e _ _ -> "If (" ++ printTree e ++ ")"
    SBlock _ -> ""
    s -> printTree s
-}

funType :: Def -> FunType
funType (DFun rt _ args _) = FunType rt $ map (\ (ADecl t _) -> t) args