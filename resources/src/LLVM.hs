{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module LLVM where

import Javalette.Abs

data Fun = Fun {funId :: Ident, funFunType :: FunType}
    deriving Show

data FunType = FunType {funRet :: Type, funParse :: [Type]}
    deriving Show

type Addr = Int

newtype Label = L { theLabel :: Int }
    deriving (Eq, Enum, Show)

data Code
    = Store Type Addr
    | Load  Type Addr
    | IConst Integer
    | DConst Double
    | Dup Type
    | Pop Type
    | Return Type
    | Call Fun
    | Label Label
    | Goto Label
    | If CmpOp Label
    | IfCmp Type CmpOp Label
    | DCmp
    | Inc Type Addr Int
    | Add Type AddOp
    | Mult Type MulOp
    | I2D
    | Comment String
    
    deriving (Show)

pattern IfZ l = If OEq l
pattern IfNZ l = If ONEq l

negateCmp :: CmpOp -> CmpOp
negateCmp cmpOp = case cmpOp of
    OEq -> ONEq
    ONEq -> OEq
    OLt -> OGtEq
    OGt -> OLtEq
    OLtEq -> OGt
    OGtEq -> OLt

flipCmp :: CmpOp -> CmpOp
flipCmp cmpOp = case cmpOp of
    OEq -> OEq
    ONEq -> ONEq
    OLt -> OGt
    OGt -> OLt
    OLtEq -> OGtEq
    OGtEq -> OLtEq

prefix :: Type -> String
prefix typ = case typ of
    Int -> "i"
    Double -> "d"
    Bool -> "i"
    Void -> ""

isByte :: Integer -> Bool
isByte i = case length (show i) of
    8 -> True
    _ -> False

class Size a where
    size :: a -> Int

instance Size Type where
    size t = case t of
        Int -> 1
        Double -> 2
        Bool -> 1
        Void -> 0

instance Size Ident where
    size _ = 0

instance (Size a, Size b) => Size (a,b) where
    size (x, y) = size x + size y

instance Size a => Size [a] where 
    size = sum . map size

instance Size FunType where
    size (FunType t ts) = size ts - size t

instance Size Fun where
    size (Fun _ ft) = size ft

class ToJVM a where
    tojvm :: a -> String

instance ToJVM Type where 
    tojvm t = case t of
        Int -> "I"
        Void -> "V"
        Double -> "D"
        Bool -> "Z"

instance ToJVM FunType where
    tojvm (FunType t ts) = "(" ++ (tojvm =<< ts) ++ ")" ++ tojvm t

instance ToJVM Fun where
    tojvm (Fun (Id f) t) = f ++ tojvm t

instance ToJVM Label where
    tojvm (L l) = "L" ++ show l

instance ToJVM CmpOp where
    tojvm cmpOp = case cmpOp of
        OLt -> "lt"
        OGt -> "gt"
        OLtEq -> "le"
        OGtEq -> "ge"
        OEq -> "eq"
        ONEq -> "ne"

instance ToJVM AddOp where
    tojvm addOp = case addOp of
        OPlus -> "add"
        OMinus -> "sub"

instance ToJVM MulOp where
    tojvm mulOp = case mulOp of
        OTimes -> "mul"
        ODiv -> "div"


instance ToJVM Code where
    tojvm code = case code of
        Store t n -> prefix t ++ "store " ++ show n
        Load t n -> prefix t ++ "load " ++ show n
        Return t -> prefix t ++ "return"
        Call f -> "invokestatic " ++ tojvm f
        DConst d -> "ldc2_w " ++ show d
        IConst i
            | i == -1 -> "iconst_m1"
            | i >= 0 && i <= 5 -> "iconst_" ++ show i
            | isByte i -> "bipush " ++ show i
            | otherwise -> "ldc " ++ show i
        Dup Double -> "dup2"
        Dup _  -> "dup"
        Pop Double -> "pop2"
        Pop _ -> "pop"
        Label l -> tojvm l ++ ":"
        Goto l -> "goto " ++ tojvm l
        If op l -> "if" ++ tojvm op ++ " " ++ tojvm l
        c@(IfCmp Double _ _) -> error $ "not allowed " ++ show c
        c@(IfCmp Void _ _) -> error $ "not allowed " ++ show c
        IfCmp _ op l -> "if_icmp" ++ tojvm op ++ " " ++ tojvm l
        DCmp -> "dcmpg"
        Inc Int a k -> "iinc " ++ show a ++ " " ++ show k
        c@Inc{} -> error $ "npt possible " ++ show c
        Add t op -> prefix t ++ tojvm op
        Mult t op -> prefix t ++ tojvm op
        I2D -> "i2d"
        Comment "" -> ""
        Comment s -> ";; " ++ s