{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Haskell.Exference.Core.Types
  ( TVarId
  , QualifiedName(..)
  , HsType (..)
  , HsTypeOffset (..)
  , Subst (..)
  , Substs
  , HsTypeClass (..)
  , HsInstance (..)
  , HsConstraint (..)
  , StaticClassEnv (..)
  , QueryClassEnv ( qClassEnv_env
                  , qClassEnv_constraints
                  , qClassEnv_inflatedConstraints
                  , qClassEnv_varConstraints )
  , constraintApplySubsts
  , inflateHsConstraints
  , applySubst
  , applySubsts
  -- , typeParser
  , containsVar
  , showVar
  , showTypedVar
  , mkQueryClassEnv
  , addQueryClassEnv
  , freeVars
  , showHsConstraint
  , TypeVarIndex
  , showHsType
#if !MIN_VERSION_base(4,8,0)
  , Alt (..)
#endif
  )
where



import Data.Char ( ord, chr, isLower, isUpper, toLower )
import Data.List ( intercalate, intersperse )
import Data.Foldable ( fold, foldMap )
import Control.Applicative ( (<$>), (<*>), (*>), (<*) )
import Data.Maybe ( maybeToList, fromMaybe )
import Data.Monoid ( Monoid(..), Any(..) )
import Control.Monad ( liftM, liftM2, MonadPlus )
import Control.Applicative ( Applicative, Alternative, empty, (<|>) )
import Control.Arrow ( first )
import Data.Orphans ()

import qualified Data.Set as S
import qualified Data.IntSet as IntSet
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as L

import Text.ParserCombinators.Parsec hiding (State, (<|>))
import Text.ParserCombinators.Parsec.Char

import Language.Haskell.Exts.Syntax ( Name (..) )

import Control.DeepSeq.Generics
import Control.DeepSeq
import GHC.Generics
import Data.Data ( Data )
import Data.Typeable ( Typeable )
import Control.Monad.Trans.MultiState
import Safe

import Debug.Hood.Observe
import Debug.Trace



#if !MIN_VERSION_base(4,8,0)
newtype Alt f a = Alt {getAlt :: f a}
  deriving (Generic, Generic1, Read, Show, Eq, Ord, Num, Enum,
            Monad, MonadPlus, Applicative, Alternative, Functor)

instance forall f a . Alternative f => Monoid (Alt f a) where
        mempty = Alt empty
        (Alt x) `mappend` (Alt y) = Alt (x <|> y)
#endif

type TVarId = Int
data Subst  = Subst {-# UNPACK #-} !TVarId !HsType
type Substs = IntMap.IntMap HsType

data QualifiedName
  = QualifiedName [String] String
  | ListCon
  | TupleCon Int
  | Cons
  deriving (Eq, Ord, Generic, Data, Typeable)

data HsType = TypeVar      {-# UNPACK #-} !TVarId
            | TypeConstant {-# UNPACK #-} !TVarId
              -- like TypeCons, for exference-internal purposes.
            | TypeCons     QualifiedName
            | TypeArrow    !HsType !HsType
            | TypeApp      !HsType !HsType
            | TypeForall   [TVarId] [HsConstraint] !HsType
  deriving (Ord, Eq, Generic, Data, Typeable)

data HsTypeOffset = HsTypeOffset !HsType {-# UNPACK #-} !Int

type TypeVarIndex l = M.Map (Name l) Int

data HsTypeClass = HsTypeClass
  { tclass_name :: QualifiedName
  , tclass_params :: [TVarId]
  , tclass_constraints :: [HsConstraint]
  }
  deriving (Eq, Show, Ord, Generic, Data, Typeable)

data HsInstance = HsInstance
  { instance_constraints :: [HsConstraint]
  , instance_tclass :: HsTypeClass
  , instance_params :: [HsType]
  }
  deriving (Eq, Show, Ord, Generic, Data, Typeable)

data HsConstraint = HsConstraint
  { constraint_tclass :: HsTypeClass
  , constraint_params :: [HsType]
  }
  deriving (Eq, Ord, Generic, Data, Typeable)

data StaticClassEnv = StaticClassEnv
  { sClassEnv_tclasses :: [HsTypeClass]
  , sClassEnv_instances :: M.Map QualifiedName [HsInstance]
  }
  deriving (Show, Generic, Data, Typeable)

data QueryClassEnv = QueryClassEnv
  { qClassEnv_env :: StaticClassEnv
  , qClassEnv_constraints :: S.Set HsConstraint
  , qClassEnv_inflatedConstraints :: S.Set HsConstraint
  , qClassEnv_varConstraints :: IntMap.IntMap (S.Set HsConstraint)
  }
  deriving (Generic)

instance NFData QualifiedName  where rnf = genericRnf
instance NFData HsType         where rnf = genericRnf
instance NFData HsTypeClass    where rnf = genericRnf
instance NFData HsInstance     where rnf = genericRnf
instance NFData HsConstraint   where rnf = genericRnf
instance NFData StaticClassEnv where rnf = genericRnf
instance NFData QueryClassEnv  where rnf = genericRnf

instance Show QualifiedName where
  show (QualifiedName ns n) = if    length n >= 2
                                 && head n == '('
                                 && last n == ')'
                              then "(" ++ intercalate "." (ns ++ [tail n])
                              else        intercalate "." (ns ++ [n])
  show ListCon              = "[]"
  show (TupleCon 0)         = "()"
  show (TupleCon i)         = "(" ++ replicate (i-1) ',' ++ ")"
  show Cons                 = "(:)"

instance Show HsType where
  showsPrec _ (TypeVar i) = showString $ showVar i
  showsPrec _ (TypeConstant i) = showString $ "C" ++ showVar i
  showsPrec d (TypeCons s) = showsPrec d s
  showsPrec d (TypeArrow t1 t2) =
    showParen (d> -2) $ showsPrec (-1) t1 . showString " -> " . showsPrec (-1) t2
  showsPrec d (TypeApp t1 t2) =
    showParen (d> -1) $ showsPrec 0 t1 . showString " " . showsPrec 0 t2
  showsPrec d (TypeForall [] [] t) = showsPrec d t
  showsPrec d (TypeForall is cs t) =
    showParen (d>0)
    $ showString ("forall " ++ intercalate ", " (showVar <$> is) ++ " . ")
    . showParen True (\x -> foldr (++) x $ intersperse ", " $ map show cs)
    . showString " => "
    . showsPrec (-2) t

showHsType :: TypeVarIndex l -> HsType -> String
showHsType convMap t = h 0 t ""
 where
  h :: Int -> HsType -> ShowS
  h _ (TypeVar i)      = showString
                       $ maybe "badNameInternalError"
                               (\(Ident _ n, _) -> n)
                       $ L.find ((i ==) .  snd)
                       $ M.toList convMap
  h _ (TypeConstant i) = showString
                       $ maybe "badNameInternalError"
                               (\(Ident _ n, _) -> n)
                       $ L.find ((i ==) .  snd)
                       $ M.toList convMap
  h _ (TypeCons s) = shows s
  h d (TypeArrow t1 t2) =
    showParen (d> -2) $ t1Shows . showString " -> " . t2Shows
    where
      t1Shows = h (-1) t1
      t2Shows = h (-1) t2
  h d (TypeApp t1 t2) =
    showParen (d> -1) $ t1Shows . showString " " . t2Shows
    where
      t1Shows = h 0 t1
      t2Shows = h 0 t2
  h d (TypeForall [] [] ty) = h d ty
  h d (TypeForall is cs ty) =
    showParen (d>0)
      $ showString ("forall " ++ intercalate ", " (showVar <$> is) ++ " . ")
      . showParen True (\x -> foldr (++) x $ intersperse ", " $ map show cs)
      . showString " => "
      . tShows
    where
      tShows = h (-2) ty

instance Observable HsType where
  observer x = observeOpaque (show x) x

-- instance Read HsType where
--   readsPrec _ = maybeToList . parseType

instance Show HsConstraint where
  show (HsConstraint c ps) = unwords $ show (tclass_name c) : map show ps

showHsConstraint :: TypeVarIndex l
                 -> HsConstraint
                 -> String
showHsConstraint convMap (HsConstraint c ps) =
  unwords $ show name : tyStrs  
 where
  name = tclass_name c
  tyStrs = showHsType convMap <$> ps
  

instance Show QueryClassEnv where
  show (QueryClassEnv _ cs _ _) = "(QueryClassEnv _ " ++ show cs ++ " _)"
instance Observable HsConstraint where
  observer x = observeOpaque (show x) x

instance Observable QueryClassEnv where
  observer x = observeOpaque (show x) x

instance Observable HsInstance where
  observer x = observeOpaque (show x) x

filterHsConstraintsByVarId :: TVarId
                           -> S.Set HsConstraint
                           -> S.Set HsConstraint
filterHsConstraintsByVarId i = S.filter
                             $ any (containsVar i) . constraint_params

containsVar :: TVarId -> HsType -> Bool
containsVar i = S.member i . freeVars

mkQueryClassEnv :: StaticClassEnv -> [HsConstraint] -> QueryClassEnv
mkQueryClassEnv sClassEnv constrs = addQueryClassEnv constrs $ QueryClassEnv {
  qClassEnv_env = sClassEnv,
  qClassEnv_constraints = S.empty,
  qClassEnv_inflatedConstraints = S.empty,
  qClassEnv_varConstraints = IntMap.empty
}

addQueryClassEnv :: [HsConstraint] -> QueryClassEnv -> QueryClassEnv
addQueryClassEnv constrs env = env {
  qClassEnv_constraints = csSet,
  qClassEnv_inflatedConstraints = inflateHsConstraints csSet,
  qClassEnv_varConstraints = helper constrs
}
  where
    csSet = S.fromList constrs `S.union` qClassEnv_constraints env
    helper :: [HsConstraint] -> IntMap.IntMap (S.Set HsConstraint)
    helper cs =
      let ids :: IntSet.IntSet
          ids = IntSet.fromList $ S.toList $ fold $ freeVars <$> (constraint_params =<< cs)
      in IntMap.fromSet (flip filterHsConstraintsByVarId
                        $ inflateHsConstraints csSet) ids

inflateHsConstraints :: S.Set HsConstraint -> S.Set HsConstraint
inflateHsConstraints = inflate (S.fromList . f)
  where
    f :: HsConstraint -> [HsConstraint]
    f (HsConstraint (HsTypeClass _ ids constrs) ps) =
      map (snd . constraintApplySubsts (IntMap.fromList $ zip ids ps)) constrs

-- uses f to find new elements. adds these new elements, and recursively
-- tried to find even more elements. will not terminate if there are cycles
-- in the application of f
inflate :: (Ord a, Show a) => (a -> S.Set a) -> S.Set a -> S.Set a
inflate f = fold . takeWhile (not . S.null) . iterate (foldMap f)

constraintApplySubst :: Subst -> HsConstraint -> HsConstraint
constraintApplySubst s (HsConstraint c ps) =
  HsConstraint c $ map (applySubst s) ps

-- returns if any change was necessary,
-- plus the (potentially changed) constraint
-- constraintApplySubst' :: Subst -> HsConstraint -> (Bool, HsConstraint)
-- constraintApplySubst' s (HsConstraint c ps) =
--   let applied = map (applySubst' s) ps
--   in (any fst applied, HsConstraint c $ snd <$> applied)

-- returns if any change was necessary,
-- plus the (potentially changed) constraint
{-# INLINE constraintApplySubsts #-}
constraintApplySubsts :: Substs -> HsConstraint -> (Any, HsConstraint)
constraintApplySubsts ss c
  | IntMap.null ss = return c
  | HsConstraint cl ps <- c =
    HsConstraint cl <$> mapM (applySubsts ss) ps

showVar :: TVarId -> String
showVar 0 = "v0"
showVar i | i<27      = [chr (ord 'a' + i - 1)]
          | otherwise = "t"++show (i-27)

showTypedVar :: forall m
              . ( MonadMultiState (M.Map TVarId HsType) m )
             => TVarId
             -> m String
showTypedVar i = do
  m <- mGet
  fromJustNote "missing collectVarTypes before showTypedVar"
    $ h <$> M.lookup i m
 where
  -- h t | traceShow (i, t) False = undefined
  h TypeVar{}          = return $ showVar i
  h TypeConstant{}     = return $ showVar i
  h (TypeCons qName) = do
    return $ case qName of
      QualifiedName _ (c:_) -> toLower c : show i
      QualifiedName{}       -> showVar i
      ListCon               -> showVar i ++ "s"
      TupleCon{}            -> showVar i
      Cons                  -> showVar i
  h TypeArrow{}        = return $ "f" ++ show i
  h (TypeApp t _)      = h t
  h (TypeForall _ _ t) = h t

-- parseType :: _ => String -> m (Maybe (HsType, String))
-- parseType s = either (const Nothing) Just
--             $ runParser (    (,)
--                          <$> typeParser
--                          <*> many anyChar)
--                         ()
--                         ""
--                         s
-- 
-- typeParser :: forall m . (_) => Parser (m HsType)
-- typeParser = parseAll
--   where
--     parseAll :: Parser (m HsType)
--     parseAll = parseUn >>= parseBin
--     parseUn :: Parser (m HsType) -- TODO: forall
--     parseUn = spaces *> (
--             try (TypeCons . QualifiedName [] <$> ((:) <$> satisfy isUpper <*> many alphaNum))
--         <|> try ((TypeVar . (\x -> x - ord 'a') . ord) <$> satisfy isLower)
--         <|>     (char '(' *> parseAll <* char ')')
--       )
--     parseBin :: HsType -> Parser HsType
--     parseBin left =
--         try (    try (TypeArrow left <$> (spaces *> string "->" *> parseAll))
--              <|>     ((TypeApp   left <$> (space *> parseUn)) >>= parseBin)
--              )
--         <|>
--         (spaces *> return left)

applySubst :: Subst -> HsType -> HsType
applySubst (Subst i t) v@(TypeVar j) = if i==j then t else v
applySubst _ c@(TypeConstant _) = c
applySubst _ c@(TypeCons _)     = c
applySubst s (TypeArrow t1 t2)  = TypeArrow (applySubst s t1) (applySubst s t2)
applySubst s (TypeApp t1 t2)    = TypeApp (applySubst s t1) (applySubst s t2)
applySubst s@(Subst i _) f@(TypeForall js cs t) = if i `elem` js
  then f
  else TypeForall js (constraintApplySubst s <$> cs) (applySubst s t)

applySubsts :: Substs -> HsType -> (Any, HsType)
applySubsts s v@(TypeVar i)      = fromMaybe (return v)
                                  $ (,) (Any True) <$> IntMap.lookup i s
applySubsts _ c@(TypeConstant _) = return c
applySubsts _ c@(TypeCons _)     = return c
applySubsts s (TypeArrow t1 t2)  = liftM2 TypeArrow (applySubsts s t1) (applySubsts s t2)
applySubsts s (TypeApp t1 t2)    = liftM2 TypeApp   (applySubsts s t1) (applySubsts s t2)
applySubsts s (TypeForall js cs t) = liftM2 (TypeForall js) 
  (sequence $ constraintApplySubsts s <$> cs)
  (applySubsts (foldr IntMap.delete s js) t)

freeVars :: HsType -> S.Set TVarId
freeVars (TypeVar i)         = S.singleton i
freeVars (TypeConstant _)    = S.empty
freeVars (TypeCons _)        = S.empty
freeVars (TypeArrow t1 t2)   = S.union (freeVars t1) (freeVars t2)
freeVars (TypeApp t1 t2)     = S.union (freeVars t1) (freeVars t2)
freeVars (TypeForall is _ t) = foldr S.delete (freeVars t) is

-- instance Monoid w => Monad ((,) w) where
--   return = (,) mempty
--   (w,x) >>= f = first (mappend w) (f x)
