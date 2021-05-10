{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wunused-top-binds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module CompileLLVM (compile, toLLVM) where


import Lens.Micro.Platform hiding (Empty)

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer.Lazy
    ( execWriter, MonadWriter(tell), Writer )
import Control.Monad.State.Lazy

import Control.Monad.RWS.Lazy

import Text.Printf
import Data.List
import Data.Maybe ( fromMaybe )
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Javalette.Abs as J
import qualified Annotated as A

type Ident = String

data SL = SL Ident Int String
    deriving Show



--type Cxts = [Block]
--type Block = [(Ident, Type)]

data St = St {
    _nextReg :: Int
 ,  _nextLabel :: Int
 ,  _funArgs :: [[Reg]]
}


-- temp : eval todo


type StringLitScanner = StateT Int (Writer (Map String SL)) ()


getStrLits :: A.Prog -> Map String SL
getStrLits (A.Program tds) =
    execWriter $ (mapM_ tdStrLits tds) `execStateT` 0

tdStrLits :: A.Special -> StringLitScanner
tdStrLits (A.FnDef _ _ _ (A.Block ss)) = mapM_ stmStrLits ss

stmStrLits :: A.Stm -> StringLitScanner
stmStrLits (A.BStmt (A.Block ss)) = mapM_ stmStrLits ss
stmStrLits (A.Cond _ s)           = stmStrLits s
stmStrLits (A.CondElse _ s1 s2)   = stmStrLits s1 >> stmStrLits s2
stmStrLits (A.While _ s)          = stmStrLits s
stmStrLits (A.SExp (A.TExpr _ e)) = expStrLits e
stmStrLits _ = pure ()

expStrLits :: A.Expr -> StringLitScanner
expStrLits (A.EApp (J.Ident "printString") [A.TExpr _ (A.EString s)]) = do
  n <- get
  modify (+1)
  tell $ Map.singleton s $ SL ("s" <> show n) (length s + 1) s
expStrLits _ = pure ()

class ToLLVM a where
  toLLVM :: a -> String

instance ToLLVM Code where
  toLLVM (Comment s)  = indent $ "; " <> s
  toLLVM (Declare t s ts) = printf "declare %s @%s(%s)" (toLLVM t) s
    (intercalate ", " $ map toLLVM ts)

  toLLVM (Define t s args code) =
    printf "define %s @%s(%s) {\n%s}" t' s args' code' where
      t' = toLLVM t
      args' = intercalate ", " $ map toLLVM args
      code' = unlines $ map toLLVM code

  toLLVM (Return t v) = indent $ printf "ret %s %s" (toLLVM t) (toLLVM v)

  toLLVM VReturn = indent $ "ret void"

  toLLVM (Label s) = s <> ":"

  toLLVM (Store src_t src_v dest_t dest_v) = indent $
    printf "store %s %s, %s %s"
    (toLLVM src_t) (toLLVM src_v) (toLLVM dest_t) (toLLVM dest_v)

  toLLVM (Alloca t i) = indent $ printf "%%%s = alloca %s" i $ toLLVM t

  toLLVM c = error $ show c


formatArgs :: [Type] -> [Val] -> String
formatArgs ts vs = intercalate ", "
  [(toLLVM t) <> " " <> (toLLVM v)| (t, v) <- zip ts vs]

-- end temp

type Compile = RWS Env Output St

newtype Env = Env {
  _strings :: Map String SL
}

data Output = Output { _code :: [Code], _typedefs :: [Code]}
  deriving Show


instance Semigroup Output where
  (Output c1 tds1) <> (Output c2 tds2) = Output (c1 ++ c2) (tds1 ++ tds2)


data Val = IntLit Integer | DoubleLit Double | RegName Reg | StringName String
  deriving Show

data Type = Int | Double | Bool | Char | Void | Str Int |
            Ptr Type | Arr Type | Custom String
  deriving (Show, Eq, Ord)

--type Compile = State St



type Reg = String

type Arg = (Type, String)

data Code = Comment String
          | Declare Type String [Type]
          | Define Type String [Arg] [Code]
          | Return Type Val
          | VReturn
          | Label String
          | Store Type Val Type Val
          | Alloca Type Reg
          | Load Reg Type Reg
          | Mul Reg Type Val Val
          | Div Reg Type Val Val
          | Mod Reg Type Val Val
          | Add Reg Type Val Val
          | Sub Reg Type Val Val
          | LTH Reg Type Val Val
          | LE  Reg Type Val Val
          | GTH Reg Type Val Val
          | GE  Reg Type Val Val
          | EQU Reg Type Val Val
          | NE  Reg Type Val Val
          | FNeg Reg Val
          | Not Reg Val
          | VCall String [Type] [Val]
          | Branch String
          | CondBranch Reg String String
          | Call Reg String Type [Type] [Val]
  deriving Show


instance Monoid Output where
  mempty = Output [] []





indent :: String -> String
indent s = if null s then s else "\t" ++ s



instance ToLLVM Type where
  toLLVM Int  = "i32"
  toLLVM Double = "double"
  toLLVM Bool = "i1"
  toLLVM Char  = "i8"
  toLLVM Void = "void"
  toLLVM (Str l) = printf "[%s x i8]" (show l)
  toLLVM (Ptr t) = toLLVM t <> "*"
  toLLVM (Arr _) = "i32*"
  toLLVM (Custom s) = '%' : s

instance ToLLVM Val where
  toLLVM (IntLit i)  = show i
  toLLVM (DoubleLit d) = show d
  toLLVM (RegName r) = '%' : r
  toLLVM (StringName s) = '@' : s

instance ToLLVM Arg where
  toLLVM (t,s) = toLLVM t <> " %" <> s

instance ToLLVM SL where 
  toLLVM (SL name len str) = printf
    "junk" name (show len) str

tBytes :: Type -> Integer
tBytes Int = 4
tBytes Double = 8
tBytes Bool = 1
tBytes Char = 1
tBytes (Ptr _) = 4
tBytes _ = error "tBytes on type that should not be possible"


  --- HELPER FUNCTIONS BELOW ---

makeLenses ''St

comment :: String -> Compile ()
comment = emit . Comment

--could use show?? TODO
emit :: Code -> Compile ()
emit c = tell $ Output [c] []

emitSpecial :: Code -> Compile ()
emitSpecial special = tell $ Output [] [special]

initState :: St
initState =  St 0 0 []

newReg :: Compile Reg
newReg = nextReg += 1 >> ("t" <>) . show <$> use nextReg

newLabel :: Compile String
newLabel = nextLabel += 1 >> ("t" <>) . show <$> use nextLabel


--todo : evaluate
grabOutput :: Compile () -> Compile [Code]
grabOutput ma = do
    s <- get
    r <- ask
    let ((), s', Output c special) = runRWS ma r s
    mapM_ emitSpecial special
    put s'
    return c

toType :: J.Type -> Type
toType J.Int     = Int
toType J.Double  = Double
toType J.Bool    = Bool
toType J.Void    = Void

getType :: A.TExpr -> Type
getType = toType . A.typeof


---- Actual codegen ----------

 --todo eval
data LLVMable = forall a. (ToLLVM a, Show a) => LL a

instance Show LLVMable where
  show (LL a) = show a

instance ToLLVM LLVMable where
  toLLVM (LL a) = toLLVM a

instance ToLLVM [LLVMable] where
  toLLVM lls = unlines $ map toLLVM lls



compile :: A.Prog  -> [LLVMable]
compile p@(A.Program specials) =
   prolog <> strs <> map LL typedefs <> map LL program
  where prolog = map LL [Declare Void      "printInt" [Int],
                         Declare Void      "printDouble" [Double],
                         Declare Void      "printString" [Ptr Char],
                         Declare Int       "readInt" [],
                         Declare Double      "readDouble" [],
                         Declare (Ptr Int) "calloc" [Int, Int]]
        strLits = getStrLits p
        strs = map LL $ Map.elems strLits
        (Output program typedefs) = snd $
          evalRWS (mapM_ compileSpecial specials) (Env strLits) initState

--Todo : fix top level generation of code. this not done yet. 
compileSpecial :: A.Special -> Compile()
compileSpecial (A.FnDef t (J.Ident s) args (A.Block  ss)) = do
  funArgs %= ((map snd args') :)
  stmList <- grabOutput $ mapM_  compileStm ss
  funArgs %= tail
  defret <- defaultRet t
  let ss' = stmList <> defret
  emit $ Define t' s args' $ Label "entry" : ss'
    where t'    = toType t
          args' = map (\(J.ADecl t (J.Ident i)) -> (toType t,i)) args

defaultRet :: J.Type -> Compile[Code]
defaultRet J.Int = pure [Return Int (IntLit 0)] 
defaultRet J.Double  = pure [Return Double (DoubleLit 0.0)] 
defaultRet J.Bool  = pure [Return Bool (IntLit 0)] 
defaultRet J.Void = pure [VReturn]


compileStm :: A.Stm -> Compile ()
compileStm A.Empty = comment "noSTM"

compileStm (A.Ret e) = do
  reg <- compileExp e
  emit $ Return (getType e) (RegName reg)

compileStm A.VRet =
  emit VReturn

compileStm (A.SExp texpr) =
  void $ compileExp texpr

--if else stm 
compileStm (A.CondElse te stm1 stm2) = do
            ifEqual <- newLabel
            ifNotEqual <- newLabel
            true <- newLabel
            false <- newLabel
            done <- newLabel
            res <- compileExp te
            cmp <- newReg
            emit $ EQU cmp Bool (RegName res) (IntLit 0)
            emit $ CondBranch cmp ifEqual ifNotEqual
            emit $ Label ifNotEqual
            compileStm stm1
            emit $ Branch done
            emit $ Label ifEqual
            compileStm stm2
            emit $ Branch done
            emit $ Label done


--if stm condition, piggyback on ifelse
compileStm (A.Cond t s1) =
  compileStm $ A.CondElse t s1 A.Empty

compileStm (A.While exp stm) =
  compileWhile exp $ compileStm stm





compileExp :: A.TExpr -> Compile Reg
compileExp (A.TExpr t (A.EVar (A.IdId i))) =
  getVar i (toType t)

compileExp (A.TExpr t (A.Neg te)) = do
  r <- compileExp te
  result <- newReg
  case t of
    J.Int -> emit $ Mul result Int (RegName r) (IntLit (-1))
    J.Double  -> emit $ FNeg result (RegName r)
  pure result



compileExp (A.TExpr _ A.ELitTrue) = mkLit Bool $ IntLit 1

compileExp (A.TExpr _ A.ELitFalse) = mkLit Bool $ IntLit 0

compileExp (A.TExpr _ (A.ELitInt i)) = mkLit Bool $ IntLit i

compileExp (A.TExpr _ (A.ELitDouble d )) = mkLit Bool $ DoubleLit d



mkLit :: Type -> Val -> Compile Reg
mkLit t v = do
  nr <- newReg
  emit $ Alloca t nr
  emit $ Store t v (Ptr t) (RegName nr)
  nr2 <- newReg
  emit $ Load nr2 t nr
  pure nr2

getVar :: J.Ident -> Type -> Compile Reg
getVar i@(J.Ident i') t = do
  fa <- gets _funArgs
  if i' `elem` head fa
    then pure i'
    else do
      nr <- newReg
      emit $ Load nr t i'
      pure nr


compileWhile :: A.TExpr -> Compile () -> Compile ()
compileWhile te c = do
  test <- newLabel
  ifequal <- newLabel
  ifnotequal <- newLabel
  done <- newLabel
  emit $ Branch test
  emit $ Label test
  res <- compileExp te
  cmp <- newReg
  emit $ EQU cmp Bool (RegName res) (IntLit 0)
  emit $ CondBranch cmp ifequal ifnotequal
  emit $ Label ifnotequal
  code <- grabOutput c
  mapM_ emit code
  emit $ Branch test
  emit $ Label ifequal
  emit $ Branch done
  emit $ Label done