{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}

-- | Extended Static Checker - Nano

module Language.Nano.ESC (verifyFile) where

import           Text.PrettyPrint.HughesPJ    (text, render, (<+>))
import           System.FilePath              (addExtension)
import           Control.Monad.State
import           Control.Applicative          ((<$>))
import qualified Control.Exception as Ex

import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Syntax
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Interface  (checkValid)
import           Language.Fixpoint.Misc       (errorstar, safeZip, sortNub)
import           Language.Nano.Types
import           Language.Nano.VCMonad
import           Data.Monoid
import           Data.Maybe                   (isJust, fromJust)

--------------------------------------------------------------------------------
-- | Top-level Verifier 
--------------------------------------------------------------------------------
verifyFile :: FilePath -> IO (F.FixResult SourcePos)
--------------------------------------------------------------------------------

verifyFile f 
  = do nano   <- parseNanoFromFile f
       forM_ nano (putStrLn . render . pp)  
       let vc  = genVC nano 
       writeFile (f `addExtension` ".vc") (render $ pp vc)
       rs     <- mapM checkVC $ obligationsVCond vc
       forM rs $ (putStrLn . render . pp)  
       return  $ mconcat rs

--------------------------------------------------------------------------------
-- | Top-level VC Generator 
--------------------------------------------------------------------------------
genVC     :: Nano -> VCond
--------------------------------------------------------------------------------
genVC pgm = execute pgm act 
  where 
    act   = mconcat <$> forM pgm (`generateVC` mempty)


-----------------------------------------------------------------------------------
-- | Top-level SMT Interface 
-----------------------------------------------------------------------------------
checkVC :: (SourcePos, F.Pred) -> IO (F.FixResult SourcePos)
-----------------------------------------------------------------------------------
checkVC z@(loc, _) 
  = do r <- checkVC' z
       putStrLn $ render $ text "checkVC" <+> pp loc <+> pp r
       return r

checkVC' (loc, p) 
  = Ex.catch (checkValid loc xts p) $ \(e :: Ex.IOException) ->
      return $ F.Crash [loc] ("VC crashes fixpoint: " ++ show e )
    where 
      xts = [ (x, F.FInt) | x <- sortNub $ F.syms p ] 

-----------------------------------------------------------------------------------
-- | Verification Condition Generator 
-----------------------------------------------------------------------------------

class IsVerifiable a where 
  generateVC :: a -> VCond -> VCM VCond 

instance IsVerifiable (Fun SourcePos) where 
  generateVC fn _   = generateFunVC fn

instance IsVerifiable a => IsVerifiable [a] where 
  generateVC xs vc  = foldM (flip generateVC) vc (reverse xs)

instance IsVerifiable (Statement SourcePos) where 
  generateVC        = generateStmtVC

instance IsVerifiable (VarDecl SourcePos) where 
  generateVC (VarDecl l x (Just e)) vc = generateAsgnVC l x e vc
  generateVC (VarDecl _ _ Nothing)  vc = return vc


-----------------------------------------------------------------------------------
generateFunVC    :: Fun SourcePos -> VCM VCond 
-----------------------------------------------------------------------------------
generateFunVC fn 
  = do _        <- setFunction fn
       let sts   = fbody fn ++ [retStmt (floc fn)] 
       vc       <- (generateAssumeVC (fpre fn) <=< generateVC sts) mempty
       vc'      <- getSideCond 
       return    $ vc <> vc'
      
retStmt l = ReturnStmt l (Just $ IntLit l 0)

-----------------------------------------------------------------------------------
generateStmtVC :: Statement SourcePos -> VCond -> VCM VCond 
-----------------------------------------------------------------------------------

-- skip
generateStmtVC (EmptyStmt _) vc 
  = return vc

-- x = e
generateStmtVC (ExprStmt _ (AssignExpr l OpAssign x e)) vc  
  = generateAsgnVC l x e vc 

-- s1;s2;...;sn
generateStmtVC (BlockStmt _ ss) vc
  = generateVC ss vc

-- if b { s1 } else { s2 }
generateStmtVC (IfStmt _ b s1 s2) vc 
  = do vcs1 <- generateStmtVC s1 vc
       vcs2 <- generateStmtVC s2 vc
       return (g vcs1 <> notg vcs2)
    where
      g = fmap (F.PImp (F.prop b))
      notg = fmap (F.PImp (F.PNot (F.prop b)))

-- if b { s1 }
generateStmtVC (IfSingleStmt l b s) vc
  = generateVC (IfStmt l b s (EmptyStmt l)) vc

-- while (cond) { s }
generateStmtVC (WhileStmt l cond s) vc 
  = do vc1 <- generateVC s ivc
       addSideCond (fmap ((F.pAnd [i,b]) `F.PImp`) vc1)
       addSideCond (fmap ((F.pAnd [i,(F.PNot b)]) `F.PImp`) vc)
       return ivc
   where 
     i = getInvariant s
     b = F.prop cond
     ivc = newVCond l i
  
-- var x1 [ = e1 ]; ... ; var xn [= en];
generateStmtVC (VarDeclStmt _ ds) vc
  = generateVC ds vc

-- assume(e)
generateStmtVC e@(ExprStmt _ (CallExpr _ _ _)) vc
  | isJust ep = generateAssumeVC (fromJust ep) vc
  where 
    ep        = getAssume e

-- assert(e)
generateStmtVC e@(ExprStmt l (CallExpr _ _ _)) vc
  | isJust ep = generateAssertVC l (fromJust ep) vc
  where 
    ep        = getAssert e

-- ignore other specification statements
generateStmtVC e@(ExprStmt _ (CallExpr _ _ _)) vc
  | isSpecification e
  = return vc

-- return e 
generateStmtVC (ReturnStmt l (Just e)) vc
  = generateReturnVC l e vc

-- No need to handle any other statements
generateStmtVC w _ 
  = convertError "generateStmtVC" w

-----------------------------------------------------------------------------------
generateAsgnVC :: F.Symbolic x => SourcePos -> x -> Expression a -> VCond -> VCM VCond
-----------------------------------------------------------------------------------

-- x = f(e)
generateAsgnVC l x (CallExpr _ (VarRef _ (Id _ f)) es) vc
  = generateFunAsgnVC l x f es vc

-- x = e
generateAsgnVC _ x e  vc
  = generateExprAsgnVC x e vc

-----------------------------------------------------------------------------------

generateAssumeVC :: F.Pred -> VCond -> VCM VCond 
generateAssumeVC pred vc = return $ fmap (F.PImp (F.prop pred)) vc

generateAssertVC :: SourcePos -> F.Pred -> VCond -> VCM VCond 
generateAssertVC s p v = return (vc1 <> v)
  where vc1 = newVCond s (F.prop p)

-- x = e; // where e is not a function call
generateExprAsgnVC :: (F.Symbolic x, F.Expression e) => x -> e -> VCond -> VCM VCond 
generateExprAsgnVC x e = return . fmap (F.subst (F.mkSubst [(F.symbol x, F.expr e)]))

-- Do the next two last: You can knock off all the tests **WITHOUT**
-- function calls (other than the spec calls -- invariant, assert, assume)
-- without implementing the two below functions.

-- x = f(e1,...,en)
generateFunAsgnVC :: (F.Symbolic x, F.Expression e) => SourcePos -> x -> String -> [e] -> VCond -> VCM VCond 
generateFunAsgnVC l x s es vc = do
  spec <- getCalleeSpec s
  let sub  = zip (map F.symbol (fargs spec)) (map F.expr es)
  let pre  = F.subst (F.mkSubst sub) (fpre spec)
  let post = F.subst (F.mkSubst ((returnSymbol, (F.expr . F.symbol) x):sub)) (fpost spec) 
  vc <- generateAssumeVC post vc
  generateAssertVC l pre vc
 -- generateAssertVC l pre <=< generateAssumeVC post vc

-- return e
generateReturnVC :: SourcePos-> Expression SourcePos -> VCond-> VCM VCond
generateReturnVC l e vc = do
  vcpost <- getFunctionPostcond
  return $ (vc <> newVCond l  (F.subst sub vcpost))
  where sub = F.mkSubst [(returnSymbol, F.expr e)]

