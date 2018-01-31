{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MonadComprehensions #-}

module Language.Haskell.Exference.TypeFromHaskellSrc
  ( ConvData(..)
  , convertTypeNoDecl
  , convertTypeNoDeclInternal
  , convertName
  , convertQName
  , convertModuleName
  , getVar
  -- , ConversionMonad
  , parseQualifiedName
  , tyVarTransform
  , haskellSrcExtsParseMode
  , findInvalidNames
  )
where



import Language.Haskell.Exts.Syntax
import qualified Language.Haskell.Exts.Parser as P

import qualified Language.Haskell.Exference.Core.Types as T
import qualified Language.Haskell.Exference.Core.TypeUtils as TU
import qualified Data.Map as M

import Control.Applicative ( (<$>), (<*>), Applicative, liftA2 )
import Data.Maybe ( fromMaybe )
import Data.List ( find )
import Control.Arrow ( (&&&) )

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.Identity
import Control.Monad.Trans.Either

import Data.List.Split ( wordsBy )
import Control.Monad.Trans.MultiRWS
import Control.Monad.Trans.MultiState ( MonadMultiState(..) )
import Data.HList.ContainsType

import Language.Haskell.Exts.Extension ( Language (..)
                                       , Extension (..)
                                       , KnownExtension (..) )

import Debug.Trace



-- type ConversionMonad = EitherT String (State (Int, ConvMap))

data ConvData l = ConvData Int (T.TypeVarIndex l)

haskellSrcExtsParseMode :: String -> P.ParseMode
haskellSrcExtsParseMode s = P.ParseMode (s++".hs")
                                      Haskell2010
                                      exts2
                                      False
                                      False
                                      Nothing
                                      False
  where
    exts1 = [ TypeOperators
            , ExplicitForAll
            , ExistentialQuantification
            , TypeFamilies
            , FunctionalDependencies
            , FlexibleContexts
            , MultiParamTypeClasses ]
    exts2 = map EnableExtension exts1

convertTypeNoDecl
  :: (Monad m, Show l, Ord l)
  => [T.HsTypeClass]
  -> Maybe (ModuleName l)
  -> [T.QualifiedName]
  -> (Type l)
  -> EitherT
       String
       (MultiRWST r w s m)
       (T.HsType, T.TypeVarIndex l)
convertTypeNoDecl tcs mn ds t =
  mapEitherT conv $ convertTypeNoDeclInternal tcs mn ds t
 where
  conv m = [ [ (r, index)
             | r <- eith
             ]
           | (eith, ConvData _ index) <- withMultiStateAS (ConvData 0 M.empty) m
           ]

convertTypeNoDeclInternal
  :: (MonadMultiState (ConvData l) m, Show l, Ord l)
  => [T.HsTypeClass]
  -> Maybe (ModuleName l) -- default (for unqualified stuff)
                          -- Nothing uses a broad search for lookups
  -> [T.QualifiedName] -- list of fully qualified data types
                                         -- (to keep things unique)
  -> (Type l)
  -> EitherT String m T.HsType
convertTypeNoDeclInternal tcs defModuleName ds ty = helper ty
 where
  helper (TyFun _ a b)      = T.TypeArrow
                              <$> helper a
                              <*> helper b
  helper (TyTuple _ _ ts)   | n <- length ts
                          = foldl T.TypeApp (T.TypeCons $ T.TupleCon n)
                            <$> mapM helper ts
  helper (TyApp _ a b)      = T.TypeApp
                              <$> helper a
                              <*> helper b
  helper (TyVar _ vname)    = do
                              i <- getVar vname
                              return $ T.TypeVar i
  helper (TyCon _ name)     = return
                          $ T.TypeCons
                          $ convertQName defModuleName ds name
  helper (TyList _ t)       = T.TypeApp (T.TypeCons T.ListCon) <$> helper t
  helper (TyParen _ t)      = helper t
  helper TyInfix{}        = left "infix operator"
  helper TyKind{}         = left "kind annotation"
  helper TyPromoted{}     = left "promoted type"
  helper (TyForall _ maybeTVars cs t) =
    T.TypeForall
      <$> case maybeTVars of
            Nothing -> return []
            Just tvs -> tyVarTransform `mapM` tvs
      <*> convertConstraint tcs defModuleName ds `mapM` (ctx cs)
      <*> helper t
      where
        ctx :: Maybe (Context l) -> [Asst l]
        ctx Nothing   = []
        ctx (Just cx) = case cx of
          CxSingle _ a  -> [a]
          CxTuple  _ as -> as
          CxEmpty  _    -> []
  helper x                = left $ "unknown type element: " ++ show x -- TODO

getVar :: (MonadMultiState (ConvData l) m, Ord l) => Name l -> m Int
getVar n = do
  ConvData next m <- mGet
  case M.lookup n m of
    Nothing -> do
      mSet $ ConvData (next+1) (M.insert n next m)
      return next
    Just i ->
      return i

-- defaultModule -> potentially-qualified-name-thingy -> exference-q-name
convertQName :: Maybe (ModuleName l) -> [T.QualifiedName] -> QName l -> T.QualifiedName
convertQName _ _ (Special _ (UnitCon _))          = T.TupleCon 0
convertQName _ _ (Special _ (ListCon _))          = T.ListCon
convertQName _ _ (Special _ (FunCon _))           = error "no support for FunCon" -- i wonder how we reach this..
convertQName _ _ (Special _ (TupleCon _ _ i))     = T.TupleCon i
convertQName _ _ (Special _ (Cons _))             = T.Cons
convertQName _ _ (Special _ (UnboxedSingleCon _)) = T.TupleCon 0
convertQName _ _ (Qual _ mn s)                = convertModuleName mn s
convertQName (Just d) _ (UnQual _ s)          = convertModuleName d s
convertQName Nothing ds (UnQual _ (Ident _ s))  = fromMaybe (T.QualifiedName [] s)
                                              $ find p ds
 where
  p (T.QualifiedName _ x) = x==s
  p _ = False
convertQName Nothing _ (UnQual _ s)           = convertName s

convertName :: Name l -> T.QualifiedName
convertName (Ident _ s)  = T.QualifiedName [] s
convertName (Symbol _ s) = T.QualifiedName [] $ "(" ++ s ++ ")"

convertModuleName :: ModuleName l -> Name l -> T.QualifiedName
convertModuleName (ModuleName _ n) (Ident _ s)  = parseQualifiedName
                                            $ n ++ "." ++ s
convertModuleName (ModuleName _ n) (Symbol _ s) = parseQualifiedName
                                            $ "(" ++ n ++ "." ++ s ++ ")"

parseQualifiedName :: String -> T.QualifiedName
parseQualifiedName s = let (prebracket, operator) = span (/='(') s
  in liftA2 T.QualifiedName init last $ wordsBy (=='.') prebracket ++ words operator

convertConstraint
  :: (MonadMultiState (ConvData l) m, Show l, Ord l)
  => [T.HsTypeClass]
  -> Maybe (ModuleName l)
  -> [T.QualifiedName]
  -> Asst l
  -> EitherT String m T.HsConstraint
convertConstraint tcs defModuleName@(Just _) ds (ClassA _ qname types)
  | str    <- convertQName defModuleName ds qname
  , ctypes <- mapM (convertTypeNoDeclInternal tcs defModuleName ds) types
  = do
      ts <- ctypes
      return $ T.HsConstraint ( fromMaybe TU.unknownTypeClass
                              $ find ((==str) . T.tclass_name)
                              $ tcs)
                              ts
convertConstraint tcs Nothing ds (ClassA _ (UnQual _ (Symbol _ "[]")) types)
  | ctypes <- mapM (convertTypeNoDeclInternal tcs Nothing ds) types
  = do
      ts <- ctypes
      return $ T.HsConstraint
                 ( fromMaybe TU.unknownTypeClass
                 $ find ((==T.ListCon) . T.tclass_name)
                 $ tcs )
                 ts
convertConstraint tcs Nothing ds (ClassA _ (UnQual _ (Ident _ name)) types)
  | ctypes <- mapM (convertTypeNoDeclInternal tcs Nothing ds) types
  = do
      ts <- ctypes
      let tcsTuples = (\tc -> (T.tclass_name tc, tc)) <$> tcs
      let searchF (T.QualifiedName _ n) = n==name
          searchF _                     = False
      let tc = fromMaybe TU.unknownTypeClass
             $ snd <$> find (searchF . fst) tcsTuples
      return $ T.HsConstraint tc ts
convertConstraint tcs _ ds (ClassA _ q@(Qual {}) types)
  | ctypes <- mapM (convertTypeNoDeclInternal tcs Nothing ds) types
  , name <- convertQName Nothing ds q
  = do
      ts <- ctypes
      return $ T.HsConstraint
                 ( fromMaybe TU.unknownTypeClass
                 $ find (\(T.HsTypeClass n _ _)
                         -> n==name) tcs
                 )
                 ts
convertConstraint _ Nothing _ cls@ClassA{} = error $ "convertConstraint" ++ show cls
convertConstraint env defModuleName ds (ParenA _ c)
  = convertConstraint env defModuleName ds c
convertConstraint _ _ _ c
  = left $ "bad constraint: " ++ show c

tyVarTransform :: (MonadMultiState (ConvData l) m, Ord l)
               => TyVarBind l
               -> EitherT String m T.TVarId
tyVarTransform (KindedVar _ _ _) = left $ "KindedVar"
tyVarTransform (UnkindedVar _ n) = getVar n

findInvalidNames :: [T.QualifiedName] -> T.HsType -> [T.QualifiedName]
findInvalidNames _ T.TypeVar {}          = []
findInvalidNames _ T.TypeConstant {}     = []
findInvalidNames valids (T.TypeCons qn) = case qn of
    n@(T.QualifiedName _ _) -> [ n | n `notElem` valids ]
    _                       -> []
findInvalidNames valids (T.TypeArrow t1 t2)   =
  findInvalidNames valids t1 ++ findInvalidNames valids t2
findInvalidNames valids (T.TypeApp t1 t2)     =
  findInvalidNames valids t1 ++ findInvalidNames valids t2
findInvalidNames valids (T.TypeForall _ _ t1) =
  findInvalidNames valids t1
