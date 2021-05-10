{-# LANGUAGE TemplateHaskell #-}

module Alpha  where

import Control.Monad
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Lens.Micro.Platform

import Annotated
import qualified Javalette.Abs as J

type Scopes = [Map J.Ident J.Ident]

data St = St { _scopes :: Scopes , _maxVar :: Int }
{-
emptySt :: St
emptySt = St [Map.empty] 0

makeLenses ''St

lookupScopes :: J.Ident -> Scopes -> J.Ident
lookupScopes i@(J.Ident s) ss = 
  let m = msum $ Map.lookup i <$> ss
  in case m of
      Nothing -> error $ "Variable " <> s <> " not found."
      Just x  -> x

newBlock :: State St ()
newBlock = scopes %= (Map.empty :)

killBlock :: State St ()
killBlock = scopes %= tail

inNewBlock :: State St a -> State St a
inNewBlock s = newBlock *> s <* killBlock

next :: State St J.Ident
next = maxVar += 1 >> J.Ident . ("v" <>) . show <$> use maxVar

newVar :: J.Ident -> State St J.Ident
newVar oldName@(J.Ident i) = do
    newName <- next
    zoom scopes $ _head %= Map.insert oldName newName
    pure newName

α_rename :: Prog -> Prog
α_rename (Program ts) = Program $ evalState st emptySt
    where st = mapM αDef ts

αDef :: TopDef -> State St TopDef
αDef d@(FnDef t i args (Block ss)) = inNewBlock $ do
    args' <- mapM (\(J.Argument t i) -> J.Argument t <$> newVar i) args
    ss'   <- mapM αStm ss
    pure $ FnDef t i args' $ Block ss'

αStm :: Stmt -> State St Stmt
αStm (BStmt (Block ss)) = inNewBlock $ BStmt . Block <$> mapM αStm ss
αStm (Decl t is) = Decl t <$> mapM αitem is
    where αitem (NoInit i) = NoInit <$> newVar i
          αitem (Init i e) = flip Init <$> αTExp e <*> newVar i
αStm (Ass i e) = Ass <$> αId i <*> αTExp e


αStm (Incr i) = Incr <$> αId i
αStm (Decr i) = Decr <$> αId i
αStm (Ret e) = Ret <$> αTExp e
αStm VRet = pure VRet
αStm (Cond e s) = Cond <$> αTExp e <*> αStm s
αStm (CondElse e s1 s2) = CondElse <$> αTExp e <*> αStm s1 <*> αStm s2
αStm (While e s) = While <$> αTExp e <*> αStm s
αStm (For t x e s) = inNewBlock $
  newVar x >> For t <$> αIdent x <*> αTExp e <*> αStm s
αStm (SExp e) = SExp <$> αTExp e
αStm s = pure s


αTExp :: TExpr -> State St TExpr
αTExp (TExpr t e) = TExpr t <$> αExp e

αExp :: Expr -> State St Expr
αExp (EVar i) = EVar <$> αId i
αExp (EApp i tes) = EApp i <$> mapM αTExp tes
αExp (Neg te) = Neg <$> αTExp te
αExp (Not te) = Not <$> αTExp te
αExp (EMul te1 op te2) = EMul <$> αTExp te1 <*> pure op <*> αTExp te2
αExp (EAdd te1 op te2) = EAdd <$> αTExp te1 <*> pure op <*> αTExp te2
αExp (ERel te1 op te2) = ERel <$> αTExp te1 <*> pure op <*> αTExp te2
αExp (EAnd te1 te2) = EAnd <$> αTExp te1 <*> αTExp te2
αExp (EOr te1 te2) = EOr <$> αTExp te1 <*> αTExp te2
αExp (ELen i) = ELen <$> αId i
αExp (EArr t is) = EArr t <$> αInds is
αExp e = pure e

αId :: Id -> State St Id
αId (IdId i) = IdId . lookupScopes i <$> use scopes
αId (IdArr i is) = (IdArr . lookupScopes i <$> use scopes) <*> αInds is

αIdent :: J.Ident -> State St J.Ident
αIdent i@(J.Ident _) = lookupScopes i <$> use scopes

αInds :: [Ind] -> State St [Ind]
αInds is = sequence [ArrInd <$> αTExp i | (ArrInd i) <- is]
-}