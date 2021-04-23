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

data ArithOp
    = EMul MulOp
    | EAdd AddOp
    deriving (Show)

newtype Label = L { theLabel :: Int }
    deriving (Eq, Enum, Show)

data Code
    = Alloca Type
    | Store Type Addr
    | Load  Type Addr
    | Call Type Addr [(Type, Addr)]
    | Label Label
    | Ret Type
    | Branch Label
    | Cmp Type CmpOp
    | Add Type AddOp
    | Mul Type MulOp
    | Neg Type
    | Not Type
    | IConst Integer
    | DConst Double
    | If 
    deriving (Show)

--pattern IfZ l = If OEq l
--pattern IfNZ l = If ONEq l

negateCmp :: CmpOp -> CmpOp
negateCmp cmpOp = case cmpOp of
    OEq -> ONEq
    ONEq -> OEq
    OLt -> OGtEq
    OGt -> OLtEq
    OLtEq -> OGt
    OGtEq -> OLt

prefix :: Type -> String
prefix typ = case typ of
    Int -> "i32"
    Double -> "f64" --"double"
    Bool -> "i1"
    Void -> "void"
    --EString -> "i8*" --maybe not estring?? todo

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
    size (LLVM.Fun _ ft) = size ft

class ToLLVM a where
    tollvm :: a -> String

instance ToLLVM Type where
    tollvm t = case t of
        Int -> "i32"
        Void -> "void"
        Double -> "f64"
        Bool -> "i1"

instance ToLLVM FunType where
    tollvm (FunType t ts) = "(" ++ (tollvm =<< ts) ++ ")" ++ tollvm t

instance ToLLVM Fun where
    tollvm (LLVM.Fun (Ident f) t) = f ++ tollvm t

instance ToLLVM Label where
    tollvm (L l) = "L" ++ show l

instance ToLLVM CmpOp where
    tollvm cmpOp = case cmpOp of
        OLt -> "lt"
        OGt -> "gt"
        OLtEq -> "le"
        OGtEq -> "ge"
        OEq -> "eq"
        ONEq -> "ne"

instance ToLLVM AddOp where
    tollvm addOp  = case addOp of
        OPlus -> "add"
        OMinus -> "sub"

instance ToLLVM MulOp where
    tollvm mulOp = case mulOp of
        OTimes -> "mul"
        ODiv -> "sdiv"
        OMod -> "srem"




instance ToLLVM Code where
    tollvm code = case code of
        Alloca t  -> "alloca " ++ show t -- ++ show n
        Store t addr -> concat ["store ", show t, ", ", show t, "* ", show addr]
        Load t addr -> concat ["load", show t, "* ", show addr]--todo, maybe done
        Call typ addr [fnty, fnpointer] -> concat ["call", show typ, show addr, "(", ")" ]
        Ret t -> "ret" ++ show t
        Branch l -> concat ["br", "label", show l ]
        Cmp typ op -> case typ of
            Int -> "icmp " ++ tollvm op ++ tollvm typ
            Double -> "fcmp " ++ tollvm op ++ tollvm typ
        Add typ op -> case typ of
            Int -> tollvm op ++ tollvm typ
            Double -> "f" ++ tollvm op ++ tollvm typ
        Mul typ op -> case typ of
            Int -> tollvm op ++ tollvm typ
            Double -> case op of
                ODiv -> "fdiv " ++ tollvm typ
                OMod -> "frem " ++ tollvm typ
                _ -> "f" ++ tollvm op ++ tollvm typ --Otherwise it is OTimes
        Neg typ -> "fneg " ++ tollvm typ
        Not typ -> concat ["xor ", show typ, " ", ", true"] -- using xor with [a, true] will always result in the inverse of a

        --Return t -> prefix t ++ "ret"   --todo
        {--
        Pop _ -> "pop"
        Label l -> tollvm l ++ ":"
        Goto l -> "goto " ++ tollvm l
        If op l -> "if" ++ tollvm op ++ " " ++ tollvm l
        c@(IfCmp Double _ _) -> error $ "not allowed " ++ show c
        c@(IfCmp Void _ _) -> error $ "not allowed " ++ show c
        IfCmp _ op l -> "if_icmp" ++ tollvm op ++ " " ++ tollvm l
        DCmp -> "dcmpg"
        Inc Int a k -> "iinc " ++ show a ++ " " ++ show k
        c@Inc{} -> error $ "npt possible " ++ show c
        Add t op -> case t of 
            Int -> tollvm op ++ prefix t
            Double -> "f" ++ tollvm op ++ prefix t   
        Mult t op -> case t of
            Int -> tollvm op ++ prefix t 
            Double -> case op of
                OTimes -> "fmul" ++ prefix t
                ODiv -> "fdiv" ++ prefix t
        I2D -> "i2d"
        Comment "" -> ""
        Comment s -> ";; " ++ s
        --}