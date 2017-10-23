{-# LANGUAGE LambdaCase #-}

module Backend.FcEvaluator where

import Backend.FcTypes

import Utils.Kind
import Utils.PrettyPrint
import Utils.SnocList
import Utils.Substitution
import Utils.Unique
import Utils.Var

import Data.Maybe
import Debug.Trace

-- * Evaluation Monad
-- ----------------------------------------------------------------------------

type FcEM = UniqueSupplyM

-- * Term Evaluation
-- ----------------------------------------------------------------------------

fcEvalTmStep :: FcTerm -> FcEM (Maybe FcTerm)
fcEvalTmStep (FcTmApp tm1 tm2) = case tm1 of
  FcTmAbs x ty tm3 -> do
    tm2' <- freshenFcVars tm2
    return $ Just $ substFcTmInTm (x |-> tm2') tm3
  -- _                -> fcEvalTmStep tm1 >>= \tm1' -> return $ Just $ FcTmApp tm1' tm2
  _                -> fcEvalTmStep tm1 >>= \case
    Nothing   -> return Nothing
    Just tm1' -> return $ Just $ FcTmApp tm1' tm2
fcEvalTmStep (FcTmTyApp tm1 ty) = case tm1 of
  FcTmTyAbs a tm2 -> return $ Just $ substFcTyInTm (a |-> ty) tm2
  _               -> fcEvalTmStep tm1 >>= \case
    Nothing   -> return Nothing
    Just tm1' -> return $ Just $ FcTmTyApp tm1' ty
fcEvalTmStep (FcTmLet x ty tm1 tm2) = do
  tm3 <- freshenFcVars (FcTmLet x ty tm1 tm1)
  return $ Just $ substFcTmInTm (x |-> tm3) tm2
fcEvalTmStep (FcTmCase tm1 pats) = if matcheablePattern tm1
  then return $ selectPattern tm1 pats
  else fcEvalTmStep tm1 >>= \case
    Nothing   -> return Nothing
    Just tm1' -> return $ Just $ FcTmCase tm1' pats
fcEvalTmStep _ = return Nothing

fcEvalTm :: FcTerm -> FcEM FcTerm
fcEvalTm tm = fcEvalTmStep tm >>= \case
  Nothing    -> return tm
  (Just tm') -> fcEvalTm tm'

matcheablePattern :: FcTerm -> Bool
matcheablePattern (FcTmDataCon _k)   = True
matcheablePattern (FcTmApp tm1 _tm2) = matcheablePattern tm1
matcheablePattern _                  = False

selectPattern :: FcTerm -> [FcAlt] -> Maybe FcTerm
selectPattern tm1 pats = do
  (subst,tm2) <- listToMaybe $ mapMaybe (matchAlt tm1) pats
  return $ applySubst subst tm2

matchAlt :: FcTerm -> FcAlt -> Maybe (FcTmSubst,FcTerm)
matchAlt tm1 (FcAlt pat tm2) = do
  subst <- matchPattern tm1 pat
  return (subst,tm2)

matchPattern :: FcTerm -> FcPat -> Maybe FcTmSubst
matchPattern (FcTmDataCon k1)  (FcConPat k2 [])
  | k1 == k2  = return mempty
  | otherwise = Nothing
matchPattern (FcTmDataCon _k)  _                = Nothing
matchPattern (FcTmApp tm1 tm2) (FcConPat k  []) = Nothing
matchPattern (FcTmApp tm1 tm2) (FcConPat k  vs) = do
  subst <- matchPattern tm1 (FcConPat k (init vs))
  return $ mappend ((last vs) |-> tm2) subst

freshenFcVars :: FcTerm -> FcEM FcTerm
freshenFcVars (FcTmAbs x1 ty tm1) = do
  x2 <- freshFcTmVar
  let tm2 = substFcTmInTm (x1 |-> (FcTmVar x2)) tm1
  FcTmAbs x2 ty <$> freshenFcVars tm2
freshenFcVars (FcTmVar x) = return $ FcTmVar x
freshenFcVars (FcTmApp tm1 tm2) = FcTmApp <$> freshenFcVars tm1 <*> freshenFcVars tm2
freshenFcVars (FcTmTyAbs a1 tm1) = do
  a2 <- freshFcTyVar (kindOf a1)
  let tm2 = substFcTyInTm (a1 |-> (FcTyVar a2)) tm1
  FcTmTyAbs a2 <$> freshenFcVars tm2
freshenFcVars (FcTmTyApp tm1 ty) = flip FcTmTyApp ty <$> freshenFcVars tm1
freshenFcVars (FcTmDataCon k) = return $ FcTmDataCon k
freshenFcVars (FcTmLet x1 ty tmL1 tmR1) = do
  x2 <- freshFcTmVar
  let tmL2 = substFcTmInTm (x1 |-> (FcTmVar x2)) tmL1
      tmR2 = substFcTmInTm (x1 |-> (FcTmVar x2)) tmR1
  FcTmLet x2 ty <$> freshenFcVars tmL2 <*> freshenFcVars tmR2
freshenFcVars (FcTmCase tm alts) = FcTmCase <$> freshenFcVars tm <*> mapM freshenFcVarsAlt alts

freshenFcVarsAlt :: FcAlt -> FcEM FcAlt
freshenFcVarsAlt (FcAlt (FcConPat k vs1) tm1) = do
  subst_vs2 <- mapM createSubst vs1
  let subst = subSnocListToSub $ listToSnocList $ map fst subst_vs2
      vs2   = map snd subst_vs2
  FcAlt (FcConPat k vs2) <$> freshenFcVars (substFcTmInTm subst tm1)
  where
    createSubst :: FcTmVar -> FcEM (FcTmSubst,FcTmVar)
    createSubst x1 = do
      x2 <- freshFcTmVar
      return ((x1 |-> (FcTmVar x2)),x2)

-- * Program Evaluation
-- ----------------------------------------------------------------------------

fcEvalPgm :: FcProgram -> FcEM FcTerm
fcEvalPgm (FcPgmDataDecl _decl pgm) = fcEvalPgm pgm -- TODO: okay to ignore data decl during eval?
fcEvalPgm (FcPgmValDecl val pgm)    = do
  subst <- fcEvalValBind val
  let pgm'  = substFcTmInPgm subst pgm
  fcEvalPgm pgm'
fcEvalPgm (FcPgmTerm tm)            = fcEvalTm tm

fcEvalValBind :: FcValBind -> FcEM FcTmSubst
fcEvalValBind (FcValBind x ty tm) = do
  tm' <- freshenFcVars (FcTmLet x ty tm tm)
  return (x |-> tm')

-- * Invoke the complete System F evaluator
-- ----------------------------------------------------------------------------

fcEvaluate :: UniqueSupply -> FcProgram -> FcTerm
fcEvaluate us pgm = fst $ flip runUniqueSupplyM us $ fcEvalPgm pgm
