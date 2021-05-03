{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module LLVM where

import Javalette.Abs

data Fun = Fun {funId :: Ident, funFunType :: FunType}
    deriving Show

data FunType = FunType {funRet :: Type, funParse :: [Type]}
    deriving Show

--type Addr = Int
type Lbl = String
type Ref = Int
--type Addr = Int
type Reg = Int
data Addr = Addr LLVMType Reg

data LLVMType = LLVMType Type
              | LLVMPtrType Type

newtype Label = L { theLabel :: Int }
    deriving (Eq, Enum, Show)



data Instructions
    = Alloca Value Type
    | Store Type Value Addr
    | Load  Value Addr
    | Call Value Type Addr [(Type, Addr)]
    | Label Label
    | Ret Type
    | Branch Label
    | Cmp Type CmpOp
    | Add Type AddOp
    | Mul Type MulOp
    | Neg Type
    | Not Type
    | IConst Integer
    | BrCond Value Label Label
    --deriving (Show)

--pattern IfZ l = If OEq l
--pattern IfNZ l = If ONEq l

data Value =
    Ref Reg             -- %r<i>
  | Glbl Reg            -- @C<i>
  | Const Integer       -- literal
  | DConst Double       -- literal
  | StrConst String     -- literal

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




instance Show Instructions where
    --Show Instructions = case Instructions of
    show (Alloca reg typ) = show reg ++ " = alloca" ++ show typ
    show (Store typ val addr ) = "store " ++ show typ ++ " " ++ show val ++ ", " ++ show addr
        --Alloca t  -> "alloca " ++ show t -- ++ show n
        
    show (Load reg addr ) = show reg ++ " = load " ++ show addr --concat ["load", show t, "* ", show addr]--todo, maybe done
    show (Call val typ addr [fnty, fnpointer] ) = "todo"
    show (Ret t ) =  "ret" ++ show t
    show (Branch l ) = concat ["br", "label", show l ]
    show (Cmp typ op) = case typ of
            Int -> "icmp " ++ tollvm op
            Double -> "fcmp " ++ tollvm op ++ show typ
            --Add r t v1 v2  -> showArith "fadd" "add" r t v1 v2
    show (Add typ op) = case typ of
            Int -> tollvm op ++ show typ
            Double -> "f" ++ tollvm op ++ show typ
    show (Mul typ op) = case typ of
            Int -> tollvm op ++ show typ
            Double -> case op of
                ODiv -> "fdiv " ++ show typ
                OMod -> "frem " ++ show typ
                _ -> "f" ++ tollvm op ++ show typ --Otherwise it is OTimes
    show (Neg typ ) = "fneg " ++ show typ
    show (Not typ ) = concat ["xor ", show typ, " ", ", true"] -- using xor with [a, true] will always result in the inverse of a
    show (BrCond val l1 l2 ) = "br i1 " ++ show val ++ ", label %" ++ show l1 ++ ", label %" ++ show l2
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


-- HELPING GARBAGE


instance Show Value where
  show (Ref i)      = "%r" ++ show i
  show (Glbl i)     = "@C" ++ show i
  show (Const i)    = show i
  show (DConst i)   = show i
  show (StrConst s) = s

instance Show LLVMType where
  show (LLVMType t)     = tollvm t
  --show (LLVMPtrType t)  = tollvm t ++ "*"

instance Show Addr where
  show (Addr t i)    = show t ++ " %r" ++ show i

--jl2llvm :: Type -> String
--jl2llvm Int   = "i32"
--jl2llvm Doub  = "double"
--jl2llvm Bool  = "i1"
--jl2llvm Void  = "void"
--jl2llvm (Arr t _) = error "jl2llvm: Array"
--jl2llvm (Fun t _) = jl2llvm t 
--jl2llvm Str   = "i8"


instance ToLLVM Type where
    tollvm t = case t of
        Int -> "i32"
        Void -> "void"
        Double -> "f64"
        Bool -> "i1"
