module Type where



import Data.Char ( ord, chr )
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.Trans.State.Strict
import Control.Applicative ( (<$>), (<*>), (*>), (<*) )

import Text.ParserCombinators.Parsec hiding (State)
import Text.ParserCombinators.Parsec.Char

import Data.Char ( isLower, isUpper )
import Data.Maybe ( maybeToList )

import Debug.Hood.Observe
import Debug.Trace



type TVarId = Int

data HsType = TypeVar TVarId
            | TypeCons String
            | TypeArrow HsType HsType
            | TypeApp   HsType HsType
            | TypeForall TVarId HsType

showVar :: TVarId -> String
showVar i = if i<26 then [chr (ord 'a' + i)] else "t"++show (i-26)

instance Show HsType where
  showsPrec _ (TypeVar i) = showString $ showVar i
  showsPrec d (TypeCons s) = showString s
  showsPrec d (TypeArrow t1 t2) =
    showParen (d> -2) $ showsPrec (-1) t1 . showString " -> " . showsPrec (-1) t2
  showsPrec d (TypeApp t1 t2) =
    showParen (d> -1) $ showsPrec 0 t1 . showString " " . showsPrec 0 t2
  showsPrec d (TypeForall i t) = showParen (d>0) $
    (showString $ "forall " ++ showVar i ++ " . ") . showsPrec 0 t

instance Observable HsType where
  observer x parent = observeOpaque (show x) x parent

instance Read HsType where
  readsPrec _ = maybeToList . parseType

parseType :: String -> Maybe (HsType, String)
parseType s = either (const Nothing) Just
            $ runParser (    (,)
                         <$> parseAll
                         <*> (many anyChar))
                        ()
                        ""
                        s
  where
    parseAll :: Parser HsType
    parseAll = parseUn >>= parseBin
    parseUn :: Parser HsType -- TODO: forall
    parseUn = spaces *> (
            try (TypeCons <$> ((:) <$> satisfy isUpper <*> many alphaNum))
        <|> try ((TypeVar . (\x -> x - ord 'a') . ord) <$> satisfy isLower)
        <|>     (char '(' *> parseAll <* char ')')
      )
    parseBin :: HsType -> Parser HsType
    parseBin left =
        try (    try (TypeArrow left <$> (spaces *> string "->" *> parseAll))
             <|>     ((TypeApp   left <$> (space *> parseUn)) >>= parseBin)
             )
        <|>
        (spaces *> return left)

arrowDepth :: HsType -> Int
arrowDepth (TypeVar _) = 1
arrowDepth (TypeCons _) = 1
arrowDepth (TypeArrow _ t) = 1 + arrowDepth t
arrowDepth (TypeApp _ _) = 1
arrowDepth (TypeForall _ t) = arrowDepth t

freeVars :: HsType -> S.Set TVarId
freeVars (TypeVar i) = S.singleton i
freeVars (TypeCons _) = S.empty
freeVars (TypeArrow t1 t2) = S.union (freeVars t1) (freeVars t2)
freeVars (TypeApp t1 t2) = S.union (freeVars t1) (freeVars t2)
freeVars (TypeForall i t) = S.delete i $ freeVars t

-- binds everything in Foralls, so there are no free variables anymore.
forallify :: HsType -> HsType
forallify t =
  let frees = freeVars t
  in foldr TypeForall t (S.toList frees)

reduceIds :: HsType -> HsType
reduceIds t = evalState (f t) (M.empty, 0)
  where
    f :: HsType -> State (M.Map TVarId TVarId, TVarId) HsType
    f (TypeVar i) = TypeVar <$> g i
    f c@(TypeCons _) = return c
    f (TypeArrow t1 t2) = TypeArrow <$> f t1 <*> f t2
    f (TypeApp t1 t2) = TypeApp <$> f t1 <*> f t2
    f (TypeForall i t) = TypeForall <$> (g i) <*> f t
    g :: TVarId -> State (M.Map TVarId TVarId, TVarId) TVarId
    g i = do
      (mapping, next) <- get
      case M.lookup i mapping of
        Nothing -> do
          put $ (M.insert i next mapping, next+1)
          return next
        Just x -> return x

incVarIds :: (TVarId -> TVarId) -> HsType -> HsType
incVarIds f (TypeVar i) = TypeVar (f i)
incVarIds f (TypeArrow t1 t2) = TypeArrow (incVarIds f t1) (incVarIds f t2)
incVarIds f (TypeApp t1 t2) = TypeApp (incVarIds f t1) (incVarIds f t2)
incVarIds f (TypeForall i t) = TypeForall (f i) (incVarIds f t)
incVarIds _ t = t

largestId :: HsType -> TVarId
largestId (TypeVar i)       = i
largestId (TypeCons _)      = 0
largestId (TypeArrow t1 t2) = largestId t1 `max` largestId t2
largestId (TypeApp t1 t2)   = largestId t1 `max` largestId t2
largestId (TypeForall _ t)  = largestId t

distinctify :: HsType -> HsType -> HsType
distinctify a b = let x = largestId a in incVarIds (+(x+1)) b
