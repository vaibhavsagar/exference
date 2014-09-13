{-# LANGUAGE PatternGuards #-}

module Language.Haskell.Exference.TypeFromHaskellSrc
  ( convertType
  , convertCType
  , convertTypeInternal
  , convertCTypeInternal
  , hsNameToString
  , hsQNameToString
  , ConvMap
  , getVar
  , ConversionMonad
  , parseConstrainedType
  )
where



import Language.Haskell.Exts.Syntax
import qualified Language.Haskell.Exts.Parser

import qualified Language.Haskell.Exference.Type as T
import qualified Language.Haskell.Exference.ConstrainedType as CT
import qualified Language.Haskell.Exference.TypeClasses as TC

import qualified Data.Map as M

import Control.Applicative ( (<$>), (<*>) )
import Data.Maybe ( fromMaybe )
import Data.List ( find )

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.Identity
import Control.Monad.Trans.Either



type ConversionMonad = StateT (Int, ConvMap) (Either String)

convertType :: Type -> Either String T.HsType
convertType t = evalStateT (convertTypeInternal t) (0, M.empty)

convertTypeInternal :: Type
                    -> ConversionMonad T.HsType
convertTypeInternal (TyFun a b) = T.TypeArrow
                                  <$> convertTypeInternal a
                                  <*> convertTypeInternal b
convertTypeInternal (TyTuple _ ts) | n <- length ts
                                   , name <- "Tuple" ++ show n
                                   = foldl T.TypeApp (T.TypeCons name)
                                     <$> mapM convertTypeInternal ts
convertTypeInternal (TyApp a b) = T.TypeApp
                                  <$> convertTypeInternal a
                                  <*> convertTypeInternal b
convertTypeInternal (TyVar vname) = do
                                      i <- getVar vname
                                      return $ T.TypeVar i
convertTypeInternal (TyCon name) = return
                                 $ T.TypeCons
                                 $ hsQNameToString name
convertTypeInternal (TyList t)   = T.TypeApp (T.TypeCons "List")
                                   <$> convertTypeInternal t
convertTypeInternal (TyParen t)  = convertTypeInternal t
convertTypeInternal (TyInfix _ _ _)  = lift $ Left "infix operator"
convertTypeInternal (TyKind _ _)     = lift $ Left "kind annotation"
convertTypeInternal (TyPromoted _)   = lift $ Left "promoted type"
convertTypeInternal (TyForall _ _ _) = lift $ Left "forall type" -- TODO
convertTypeInternal x                = lift $ Left $ "unknown type element: " ++ show x -- TODO

convertCType :: TC.StaticContext -> Type -> Either String CT.HsConstrainedType
convertCType context qt = evalStateT (convertCTypeInternal context qt) (0, M.empty)

convertCTypeInternal :: TC.StaticContext
       -> Type
       -> ConversionMonad CT.HsConstrainedType
convertCTypeInternal context (TyForall Nothing assertions t)
  = CT.HsConstrainedType <$> (mapM (convertConstraint context) assertions)
                         <*> (convertTypeInternal t)
convertCTypeInternal _ (TyForall _ _ _) = lift $ Left $ "forall"
convertCTypeInternal _ t = CT.HsConstrainedType [] <$> convertTypeInternal t

type ConvMap = M.Map Name Int

getVar :: Monad m => Name -> StateT (Int, ConvMap) m Int
getVar n = do
  (next, m) <- get
  case M.lookup n m of
    Nothing -> do
      put (next+1, M.insert n next m)
      return next
    Just i ->
      return i


hsQNameToString :: QName -> String
hsQNameToString (Special UnitCon) = "Unit"
hsQNameToString (Special ListCon) = "List"
hsQNameToString (Special FunCon)  = "Function" -- TODO: this is wrong (probably)
hsQNameToString (Special (TupleCon _ i)) = "Tuple" ++ show i
hsQNameToString (Special Cons)    = undefined
hsQNameToString (Special UnboxedSingleCon) = undefined
hsQNameToString (Qual _ s) = hsNameToString s -- yeah, ignore that full qualification
hsQNameToString (UnQual s) = hsNameToString s

hsNameToString :: Name -> String
hsNameToString (Ident s) = s
hsNameToString (Symbol s) = s

convertConstraint :: TC.StaticContext
                  -> Asst
                  -> ConversionMonad TC.Constraint
convertConstraint context (ClassA qname types)
  | str <- hsQNameToString qname
  , ctypes <- mapM convertTypeInternal types
  = TC.Constraint ( fromMaybe TC.unknownTypeClass
                  $ find ((==str).TC.tclass_name)
                  $ TC.context_tclasses context) <$> ctypes
convertConstraint context (ParenA c) = convertConstraint context c
convertConstraint _ c = lift $ Left $ "bad constraint: " ++ show c

parseConstrainedType :: TC.StaticContext -> String -> Either String CT.HsConstrainedType
parseConstrainedType c s = case Language.Haskell.Exts.Parser.parseType s of
  f@(Language.Haskell.Exts.Parser.ParseFailed _ _) -> Left $ show f
  Language.Haskell.Exts.Parser.ParseOk t -> convertCType c t
