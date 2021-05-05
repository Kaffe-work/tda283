module Annotated where

import Javalette.Abs (Ident, Arg, Type, AddOp, MulOp, CmpOp)

data Prog = Program [TopDef]
  deriving (Eq, Ord, Show, Read)

data TopDef = FnDef Type Ident [Arg] Blk
  deriving (Eq, Ord, Show, Read)

data Blk = Block [Stm]
  deriving (Eq, Ord, Show, Read)

data Ind = ArrInd TExpr
  deriving (Eq, Ord, Show, Read)

data Id = IdArr Ident [Ind] | IdId Ident
  deriving (Eq, Ord, Show, Read)

data Stm
    = Empty
    | BStmt Blk
    | Decl Type [Item]
    | Ass Id TExpr
    | Incr Id
    | Decr Id
    | Ret TExpr
    | VRet
    | Cond TExpr Stm
    | CondElse TExpr Stm Stm
    | While TExpr Stm
    | For Type Ident TExpr Stm
    | SExp TExpr
  deriving (Eq, Ord, Show, Read)

data Item = NoInit Ident | Init Ident TExpr
  deriving (Eq, Ord, Show, Read)

data TExpr = TExpr { typeof :: Type, expr :: Expr }
  deriving (Eq, Ord, Show, Read)

data Expr
    = ELen      Id
    | EVar      Id
    | ELitInt   Integer
    | ELitDoub  Double
    | ELitTrue
    | ELitFalse
    | EApp Ident [TExpr]
    | EString    String
    | Neg TExpr
    | Not TExpr
    | EMul TExpr MulOp TExpr
    | EAdd TExpr AddOp TExpr
    | ERel TExpr CmpOp TExpr
    | EAnd TExpr TExpr
    | EOr TExpr TExpr
  deriving (Eq, Ord, Show, Read)
