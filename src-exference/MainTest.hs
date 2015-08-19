{-# LANGUAGE GADTs #-}
{-# LANGUAGE MonadComprehensions #-}

module MainTest
  ( printAndStuff
  , printCheckExpectedResults
  , printStatistics
  , printMaxUsage
  , printSearchTree
  , filterBindingsSimple -- TODO: refactor/move this
  )
where



import Language.Haskell.Exference.Core ( ExferenceHeuristicsConfig(..)
                                      , findExpressionsWithStats )
import Language.Haskell.Exference
import Language.Haskell.Exference.ExpressionToHaskellSrc
import Language.Haskell.Exference.BindingsFromHaskellSrc
import Language.Haskell.Exference.ClassEnvFromHaskellSrc
import Language.Haskell.Exference.TypeFromHaskellSrc
import Language.Haskell.Exference.TypeDeclsFromHaskellSrc
import Language.Haskell.Exference.Core.FunctionBinding

import Language.Haskell.Exference.Core.Types
import Language.Haskell.Exference.Core.TypeUtils
import Language.Haskell.Exference.Core.Expression
import Language.Haskell.Exference.Core.ExferenceStats
import Language.Haskell.Exference.Core.SearchTree

import Control.DeepSeq

import Control.Applicative ( (<$>), (<*>) )
import Control.Arrow ( second, (***) )
import Control.Monad ( when, forM_, guard, forM, mplus, mzero )
import Data.Functor.Identity ( Identity, runIdentity )
import Data.List ( sortBy, find, intercalate, maximumBy )
import Data.Ord ( comparing )
import Text.Printf
import Data.Maybe ( listToMaybe, fromMaybe, maybeToList, catMaybes )
import Data.Either ( lefts, rights )
import Control.Monad.Writer.Strict
import qualified Data.Map as M
import qualified Data.IntMap as IntMap
import Data.Tree ( drawTree )
import qualified ListT

import Control.Monad.Trans.MultiRWS
import Data.HList.ContainsType

import Language.Haskell.Exts.Syntax ( Module(..), Decl(..), ModuleName(..) )
import Language.Haskell.Exts.Parser ( parseModuleWithMode
                                    , parseModule
                                    , ParseResult (..)
                                    , ParseMode (..) )
import Language.Haskell.Exts.Extension ( Language (..)
                                       , Extension (..)
                                       , KnownExtension (..) )

-- import Data.PPrint

import Debug.Hood.Observe
import Debug.Trace



checkData :: [(String, Bool, Bool, String, [String], [String])]
checkData =
  [ (,,,,,) "showmap"    False False "(Text.Show.Show b) => (a -> b) -> [a] -> [String]"
                                     ["\\b -> Data.Functor.fmap (\\g -> Text.Show.show (b g))"
                                     ,"\\b -> (\\c -> ((Control.Monad.>>=) c) (\\g -> Control.Applicative.pure (Text.Show.show (b g))))"]
                                     []
  , (,,,,,) "ffbind"     False False "(a -> t -> b) -> (t -> a) -> (t -> b)"
                                     ["\\b -> (\\c -> (\\d -> (b (c d)) d))"]
                                     []
  , (,,,,,) "join"       False False "(Monad m) => m (m a) -> m a"
                                     ["\\b -> ((Control.Monad.>>=) b) (\\f -> f)"]
                                     ["join"]
  , (,,,,,) "fjoin"      False False "(t -> (t -> a)) -> t -> a"
                                     ["\\b -> (\\c -> (b c) c)"]
                                     []
  , (,,,,,) "zipThingy"  False False "[a] -> b -> [(a, b)]"
                                     ["\\b -> (\\c -> ((Data.Functor.fmap (\\g -> ((,) g) c)) b)"
                                     ,"\\b -> (\\c -> (Data.List.zip b) (Control.Applicative.pure c))"]
                                     []
  , (,,,,,) "pmatch"     False True  "Data.Maybe.Maybe a -> a -> a"
                                     ["\\b -> (\\c -> ((Data.Maybe.maybe c) (\\h -> h)) b)"
                                     ,"\\b -> (\\c -> case b of { Data.Maybe.Just e -> e; Data.Maybe.Nothing  -> c })"]
                                     []
  --, (,,,,,) "pmatch2"    False True  "Tuple2 (Either a b) c -> Tuple2 (Maybe (Tuple2 a c)) (Maybe (Tuple2 b c))"
  --                                  []
  --                                   []
  , (,,,,,) "stateRun"   True  False "Control.Monad.State.State a b -> a -> b"
                                     ["\\b -> (\\c -> let (Control.Monad.State.State e) = b in let ((,) h i) = e c in h)"]
                                     []
  , (,,,,,) "fst"        True  False "(a, b) -> a"
                                     ["\\b -> let ((,) d e) = b in d"]
                                     []
  --, (,,,,,) "ffst"       True False  "(a -> Tuple b c) -> a -> b"
  , (,,,,,) "snd"        True  False "(a, b) -> b"
                                     ["\\b -> let ((,) d e) = b in e"]
                                     []
  , (,,,,,) "quad"       False False "a -> ((a, a), (a, a))"
                                     ["\\b -> ((,) (((,) b) b)) (((,) b) b)"]
                                     []
  -- , (,,,,,) "fswap"     False False  "(a -> Tuple b c) -> a -> Tuple c b"
  , (,,,,,) "liftBlub"   False False "Monad m => m a -> m b -> (a -> b -> m c) -> m c"
                                     ["\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) b) (\\h -> ((Control.Monad.>>=) c) (d h))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) c) (\\h -> ((Control.Monad.>>=) b) (\\l -> (d l) h))))"]
                                     []
  , (,,,,,) "stateBind"  False False "Control.Monad.State.State s a -> (a -> Control.Monad.State.State s b) -> Control.Monad.State.State s b"
                                     ["\\b -> (\\c -> let (Control.Monad.State.State e) = b in Control.Monad.State.State (\\g -> let ((,) k l) = e g in let (Control.Monad.State.State o) = c k in o l))"]
                                     []
  , (,,,,,) "dbMaybe"    False False "Data.Maybe.Maybe a -> Data.Maybe.Maybe (a, a)"
                                     ["Data.Functor.fmap (\\f -> ((,) f) f)"
                                     ,"\\b -> ((Control.Applicative.liftA2 (\\g -> (\\h -> ((,) h) g))) b) b"
                                     ,"\\b -> ((Control.Monad.>>=) b) (\\f -> Control.Applicative.pure (((,) f) f))"]
                                     []
  , (,,,,,) "tupleShow"  False False "(Text.Show.Show a, Text.Show.Show b) => (a, b) -> String"
                                     ["Text.Show.show"
                                     ,"\\b -> let ((,) d e) = b in Text.Show.show (((,) d) e)"]
                                     []
  , (,,,,,) "FloatToInt" False False "Float -> Int"
                                     [ "Prelude.round"
                                     , "Prelude.floor"
                                     , "Prelude.truncate"
                                     , "Prelude.ceiling"
                                     ]
                                     []
  , (,,,,,) "FloatToIntL" False False "[Float] -> [Int]"
                                     ["Data.Functor.fmap Prelude.round"
                                     ,"Data.Functor.fmap Prelude.floor"
                                     ,"Data.Functor.fmap Prelude.ceiling"
                                     ,"Data.Functor.fmap Prelude.truncate"
                                     ,"\\b -> ((>>=) b) (\\f -> Control.Applicative.pure (Prelude.truncate f))" -- this is kind of ugly
                                     ]
                                     []
  , (,,,,,) "longApp"    False False "a -> b -> c -> (a -> b -> d) -> (a -> c -> e) -> (b -> c -> f) -> (d -> e -> f -> g) -> g"
                                     ["\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> (\\h -> ((h ((e b) c)) ((f b) d)) ((g c) d)))))))"]
                                     []
  , (,,,,,) "liftSBlub"  False False "(Monad m, Monad n) => ([a] -> b -> c) -> m [n a] -> m (n b) -> m (n c)"
                                     ["\\b -> Control.Applicative.liftA2 (\\i -> (\\j -> ((Control.Monad.>>=) (Data.Traversable.sequenceA i)) (\\o -> ((Control.Monad.>>=) j) (\\s -> Control.Applicative.pure ((b o) s)))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Applicative.liftA2 (\\i -> (\\j -> ((Control.Monad.>>=) (Data.Traversable.sequenceA j)) (\\o -> ((Control.Monad.>>=) i) (\\s -> Control.Applicative.pure ((b o) s)))))) d) c))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) c) (\\h -> (Data.Functor.fmap (\\l -> ((Control.Monad.>>=) (Data.Traversable.sequenceA h)) (\\q -> (Data.Functor.fmap (b q)) l))) d)))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> (Data.Functor.fmap (\\l -> ((Control.Monad.>>=) (Data.Traversable.sequenceA l)) (\\q -> (Data.Functor.fmap (b q)) h))) c)))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> (Data.Functor.fmap (\\l -> ((Control.Monad.>>=) h) (\\p -> (Data.Functor.fmap (\\t -> (b t) p)) ((Data.Traversable.mapM (\\z -> z)) l)))) c)))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> ((Control.Monad.>>=) c) (\\l -> Control.Applicative.pure (((Control.Monad.>>=) h) (\\q -> (Data.Functor.fmap (\\u -> (b u) q)) ((Data.Traversable.mapM (\\t0 -> t0)) l)))))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) c) (\\h -> ((Control.Monad.>>=) d) (\\l -> Control.Applicative.pure (((Control.Monad.>>=) l) (\\q -> (Data.Functor.fmap (\\u -> (b u) q)) ((Data.Traversable.mapM (\\t0 -> t0)) h)))))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) c) (\\h -> ((Control.Monad.>>=) d) (\\l -> Control.Applicative.pure (((Control.Monad.>>=) l) (\\q -> (Data.Functor.fmap (\\u -> (b u) q)) (sequence h)))))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> ((Control.Monad.>>=) c) (\\l -> Control.Applicative.pure (((Control.Monad.>>=) h) (\\q -> (Data.Functor.fmap (\\u -> (b u) q)) (sequence l)))))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> (Data.Functor.fmap (\\l -> ((Control.Monad.>>=) ((Data.Traversable.mapM (\\t -> t)) l)) (\\r -> (Data.Functor.fmap (b r)) h))) c)))"]
                                     []
  , (,,,,,) "liftSBlubS" False False "Monad m => ([a] -> b -> c) -> m [Data.Maybe.Maybe a] -> m (Data.Maybe.Maybe b) -> m (Data.Maybe.Maybe c)"
                                     ["\\b -> Control.Applicative.liftA2 (\\i -> (\\j -> ((Control.Monad.>>=) j) (\\n -> (Data.Functor.fmap (\\r -> (b r) n)) (Data.Traversable.sequenceA i))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Applicative.liftA2 (\\i -> (\\j -> ((Control.Monad.>>=) i) (\\n -> (Data.Functor.fmap (\\r -> (b r) n)) (Data.Traversable.sequenceA j))))) d) c))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) c) (\\h -> (Data.Functor.fmap (\\l -> ((Control.Monad.>>=) (Data.Traversable.sequenceA h)) (\\q -> (Data.Functor.fmap (b q)) l))) d)))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> (Data.Functor.fmap (\\l -> ((Control.Monad.>>=) (Data.Traversable.sequenceA l)) (\\q -> (Data.Functor.fmap (b q)) h))) c)))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) c) (\\h -> (Data.Functor.fmap (\\l -> ((Control.Monad.>>=) (Prelude.sequence h)) (\\q -> (Data.Functor.fmap (b q)) l))) d)))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> (Data.Functor.fmap (\\l -> ((Control.Monad.>>=) h) (\\p -> (Data.Functor.fmap (\\t -> (b t) p)) ((Data.Traversable.mapM (\\z -> z)) l)))) c)))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> ((Control.Monad.>>=) c) (\\l -> Control.Applicative.pure (((Control.Monad.>>=) h) (\\q -> (Data.Functor.fmap (\\u -> (b u) q)) ((Data.Traversable.mapM (\\t0 -> t0)) l)))))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) c) (\\h -> ((Control.Monad.>>=) d) (\\l -> Control.Applicative.pure (((Control.Monad.>>=) l) (\\q -> (Data.Functor.fmap (\\u -> (b u) q)) ((Data.Traversable.mapM (\\t0 -> t0)) h)))))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) c) (\\h -> ((Control.Monad.>>=) d) (\\l -> Control.Applicative.pure (((Control.Monad.>>=) l) (\\q -> (Data.Functor.fmap (\\u -> (b u) q)) (sequence h)))))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> ((Control.Monad.>>=) c) (\\l -> Control.Applicative.pure (((Control.Monad.>>=) h) (\\q -> (Data.Functor.fmap (\\u -> (b u) q)) (sequence l)))))))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (\\h -> (Data.Functor.fmap (\\l -> ((Control.Monad.>>=) ((Data.Traversable.mapM (\\t -> t)) l)) (\\r -> (Data.Functor.fmap (b r)) h))) c)))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Monad.>>=) d) (Data.Traversable.mapM (\\l -> (Data.Functor.fmap (\\p -> (b (fold ((Data.Traversable.mapM (\\w -> w)) p))) l)) c))))"]
                                     []
  , (,,,,,) "joinBlub"   False False "Monad m => [Decl] -> (Decl -> m [FunctionBinding]) -> m [FunctionBinding]"
                                     ["\\b -> (\\c -> ((Control.Monad.>>=) ((Data.Traversable.traverse c) b)) (\\i -> Control.Applicative.pure (Control.Monad.join i)))"
                                     ,"\\b -> (\\c -> ((Control.Monad.>>=) ((Data.Traversable.mapM c) b)) (\\i -> Control.Applicative.pure (((Control.Monad.>>=) i) (\\q -> q))))"
                                     ,"\\b -> (\\c -> (Data.Functor.fmap (\\g -> ((Control.Monad.>>=) g) (\\k -> k))) ((Data.Traversable.mapM c) b))"
                                     ,"\\b -> (\\c -> ((Control.Monad.>>=) ((Data.Traversable.mapM c) b)) (\\l -> Control.Applicative.pure (((Control.Monad.>>=) l) (\\q -> q))))"
                                     ,"\\b -> (\\c -> ((Control.Monad.>>=) ((Data.Traversable.mapM c) b)) (\\l -> Control.Applicative.pure (concat l)))"
                                     ,"\\b -> (\\c -> ((Control.Monad.>>=) ((Data.Traversable.mapM c) b)) (\\i -> (Data.Traversable.mapM (\\p -> p)) (((Control.Monad.>>=) i) (Data.Functor.fmap Control.Applicative.pure))))"]
                                     []
  , (,,,,,) "liftA2"     False False "Applicative f => (a -> b -> c) -> f a -> f b -> f c"
                                     ["\\b -> (\\c -> (Control.Applicative.<*>) (((Control.Applicative.<*>) (Control.Applicative.pure b)) c))"
                                     ,"\\b -> (\\c -> (\\d -> ((Control.Applicative.<*>) ((Data.Functor.fmap (\\j -> (\\k -> (b k) j))) d)) c))"
                                     ,"\\b -> (\\c -> (Control.Applicative.<*>) ((Data.Functor.fmap b) c))"]
                                     ["liftA2", "liftA3"]
  , (,,,,,) "runEitherT" False False "Monad m => [D] -> (D -> Control.Monad.Trans.Either.EitherT e m [FB]) -> ([FB] -> [FB]) -> m [Data.Either.Either e [FB]]"
                                     ["\\b -> (\\c -> (\\d -> (Data.Traversable.traverse (\\h -> Control.Monad.Trans.Either.runEitherT (((Control.Monad.>>=) (c h)) (\\n -> Control.Applicative.pure (d n))))) b))"
                                     ,"\\b -> (\\c -> (\\d -> (Data.Traversable.traverse (\\h -> Control.Monad.Trans.Either.runEitherT ((Data.Functor.fmap d) (c h)))) b))"
                                     ,"\\b -> (\\c -> (\\d -> (Data.Traversable.mapM (\\h -> Control.Monad.Trans.Either.runEitherT ((Data.Functor.fmap d) (c h)))) b))"]
                                     []
  , (,,,,,) "constr"     False False "(Monad m, Ord e) => ((e -> Data.Either.Either e TC) -> A -> Control.Monad.Trans.Either.EitherT e m C) -> Data.Either.Either e TC -> Data.Map.Map e (Data.Either.Either e TC) -> [A] -> Control.Monad.Trans.Either.EitherT e m [C]"
                                     ["\\b -> (\\c -> (\\d -> Data.Traversable.traverse (b (\\m -> (Data.Maybe.fromMaybe c) ((Data.Map.lookup m) d)))))"
                                     ,"\\b -> (\\c -> (\\d -> Data.Traversable.mapM (b (\\m -> (Data.Maybe.fromMaybe c) ((Data.Map.lookup m) d)))))"
                                     ,"\\b -> (\\c -> (\\d -> Data.Traversable.mapM (b (\\m -> ((Data.Maybe.maybe c) (\\r -> r)) ((Data.Map.lookup m) d)))))"]
                                     []
  , (,,,,,) "fmapmap"    False False "Monad m => T -> [N] -> (CT -> N -> FB) -> (SC -> T -> m CT) -> SC -> m [FB]"
                                     ["\\b -> (\\c -> (\\d -> (\\e -> (\\f -> ((Control.Monad.>>=) ((e f) b)) (\\l -> (Data.Traversable.traverse (\\p -> Control.Applicative.pure ((d l) p))) c)))))"
                                     ,"\\b -> (\\c -> (\\d -> (\\e -> (\\f -> ((>>=) ((e f) b)) (\\l -> (Data.Traversable.traverse (\\p -> pure ((d l) p))) c)))))"
                                     ,"\\b -> (\\c -> (\\d -> (\\e -> (\\f -> ((Control.Monad.>>=) ((e f) b)) (\\l -> (Data.Traversable.mapM (\\p -> Control.Applicative.pure ((d l) p))) c)))))"
                                     ,"\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (Data.Traversable.mapM (\\j -> (Data.Functor.fmap (\\n -> (d n) j)) ((e f) b))) c))))"]
                                     []
  , (,,,,,) "fmapmap2"   False False "Monad m => T -> SC -> (T -> m [FB] -> m [FB]) -> [N] -> (SC -> T -> m CT) -> (CT -> N -> FB) -> m [FB]"
                                     ["\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> (d b) ((Data.Traversable.traverse (\\m -> ((Control.Monad.>>=) ((f c) b)) (\\s -> Control.Applicative.pure ((g s) m)))) e))))))"
                                     ,"\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> (d b) ((Data.Traversable.traverse (\\m -> (Data.Functor.fmap (\\q -> (g q) m)) ((f c) b))) e))))))"
                                     ,"\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> (d b) ((Data.Traversable.mapM (\\m -> (Data.Functor.fmap (\\s -> (g s) m)) ((f c) b))) e))))))"
                                     ,"\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> (d b) ((Data.Traversable.mapM (\\m -> (Data.Functor.fmap (\\q -> (g q) m)) ((f c) b))) e))))))"
                                     ,"\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> (d b) ((Data.Traversable.mapM (\\m -> ((Control.Monad.>>=) ((f c) b)) (\\s -> Control.Applicative.pure ((g s) m)))) e))))))"]
                                     []
  , (,,,,,) "contRet"    False False "a -> Control.Monad.Trans.Cont.Cont r a"
                                     ["\\b -> Control.Monad.Trans.Cont.Cont (\\e -> e b)"]
                                     []
  , (,,,,,) "contBind"   False False "Control.Monad.Trans.Cont.Cont r a -> (a -> Control.Monad.Trans.Cont.Cont r b) -> Control.Monad.Trans.Cont.Cont r b"
                                     ["\\b -> (\\c -> let (Control.Monad.Trans.Cont.Cont e) = b in Control.Monad.Trans.Cont.Cont (\\g -> e (\\j -> let (Control.Monad.Trans.Cont.Cont n) = c j in n g)))"]
                                     []
  , (,,,,,) "ap"         False False "Monad m => m (a->b) -> m a -> m b"
                                     ["(Control.Applicative.<*>)"]
                                     []
  ]

{-
  , (,) "liftBlub"
    (ExpLambda 1
      (ExpLambda 2
        (ExpLambda 3
          (ExpApply
            (ExpApply (ExpLit "(>>=)") (ExpVar 1))
            (ExpLambda 7
              (ExpApply
                (ExpApply (ExpLit "(>>=)") (ExpVar 2))
                (ExpLambda 11
                  (ExpApply
                    (ExpApply (ExpVar 3) (ExpVar 7))
                    (ExpVar 11)))))))))
-}

exampleInput :: [(String, Bool, Bool, String)]
exampleInput = 
  [ (,,,) "State"      False False "(s -> (a, s)) -> State s a"
  , (,,,) "showmap"    False False "(Show b) => (a -> b) -> [a] -> [String]"
  , (,,,) "ffbind"     False False "(a -> t -> b) -> (t -> a) -> (t -> b)"
  , (,,,) "join"       False False "(Monad m) => m (m a) -> m a"
  , (,,,) "fjoin"      False False "(t -> (t -> a)) -> t -> a"
  , (,,,) "zipThingy"  False False "[a] -> b -> [(a, b)]"
  , (,,,) "stateRun"   True  False "State a b -> a -> b"
  , (,,,) "fst"        True  False "(a, b) -> a"
  , (,,,) "ffst"       True  False "(a -> (b, c)) -> a -> b"
  , (,,,) "snd"        True  False "(a, b) -> b"
  , (,,,) "quad"       False False "a -> ((a, a), (a, a))"
  , (,,,) "fswap"      False False "(a -> (b, c)) -> a -> (c, b)"
  , (,,,) "liftBlub"   False False "Monad m => m a -> m b -> (a -> b -> m c) -> m c"
  , (,,,) "stateBind"  False False "State s a -> (a -> State s b) -> State s b"
  , (,,,) "dbMaybe"    False False "Maybe a -> Maybe (a, a)"
  , (,,,) "tupleShow"  False False "Show a, Show b => (a, b) -> String"
  , (,,,) "FloatToInt" False False "Float -> Int"
  , (,,,) "FloatToIntL" False False "[Float] -> [Int]"
  , (,,,) "longApp"    False False "a -> b -> c -> (a -> b -> d) -> (a -> c -> e) -> (b -> c -> f) -> (d -> e -> f -> g) -> g"
  , (,,,) "liftSBlub"  False False "Monad m, Monad n => ([a] -> b -> c) -> m ([n a]) -> m (n b) -> m (n c)"
  , (,,,) "liftSBlubS" False False "Monad m => (List a -> b -> c) -> m ([Maybe a]) -> m (Maybe b) -> m (Maybe c)"
  , (,,,) "joinBlub"   False False "Monad m => [Decl] -> (Decl -> m [FunctionBinding] -> m [FunctionBinding]"
  , (,,,) "liftA2"     False False "Applicative f => (a -> b -> c) -> f a -> f b -> f c"
  ]

filterBindings :: (MonadMultiState QNameIndex m, Functor m)
               => (QualifiedName -> Bool)
               -> [FunctionBinding]
               -> m [FunctionBinding]
filterBindings p = filterM $ \(_, qnid, _, _, _) ->
  maybe False p <$> lookupQNameId qnid

filterBindingsSimple :: (MonadMultiState QNameIndex m, Functor m)
                     => [String]
                     -> [FunctionBinding]
                     -> m [FunctionBinding]
filterBindingsSimple es = filterBindings $ \n -> case n of
  QualifiedName _ name -> name `notElem` es
  _                    -> True

checkInput :: ( m ~ MultiRWST r w s m0
              , Monad m0
              , Functor m0
              , ContainsType QNameIndex s
              , ContainsType TypeDeclMap r
              )
           => ExferenceHeuristicsConfig
           -> EnvDictionary
           -> String
           -> Bool
           -> Bool
           -> [String]
           -> m ExferenceInput
checkInput heuristics (bindings, deconss, sEnv) typeStr allowUnused patternM hidden = do
  tDeclMap <- mAsk
  ty <- unsafeReadType (sClassEnv_tclasses sEnv) exampleDataTypes tDeclMap typeStr
  filteredBindings <- filterBindingsSimple ("fix":hidden) bindings
  qNameIndex <- mGet
  return $ ExferenceInput
    ty
    filteredBindings
    deconss
    sEnv
    allowUnused
    False
    8192
    patternM
    qNameIndex
    20000
    (Just 8192)
    heuristics

exampleDataTypes :: [QualifiedName]
exampleDataTypes
  = parseQualifiedName <$> [ "Data.String.String"
                           , "Prelude.Float"
                           , "Data.Int.Int"
                           , "Data.Bool.Bool"
                           ]

checkExpectedResults :: forall m m0 r w s
                      . ( m ~ MultiRWST r w s m0
                        , Monad m0
                        , Functor m0
                        , ContainsType QNameIndex s
                        , ContainsType TypeDeclMap r
                        )
                     => ExferenceHeuristicsConfig
                     -> EnvDictionary
                     -> m [ ( String -- ^ name
                            , [String] -- ^ expected
                            , Maybe ( (Expression, ExferenceStats)
                                      -- ^ first
                                    , Maybe (Int, ExferenceStats)
                                    ) -- ^ index and stats of expected
                            )]
checkExpectedResults heuristics env = mapMultiRWST (return . runIdentity)
                                      -- for lazyness, we drop the IO
                                    $ sequence
                                    $ do
  (name, allowUnused, patternM, typeStr, expected, hidden) <- checkData
  return $ do
    input <- checkInput heuristics env typeStr allowUnused patternM hidden
    let getExp :: Int
               -> [(Expression, [HsConstraint], ExferenceStats)]
               -> MultiRWST r w s Identity (Maybe (Int, ExferenceStats))
        getExp _ [] = return $ Nothing
        getExp n ((e, _, s):r) = do
          eStr <- showExpression $ simplifyEta $ simplifyLets $ e
          if eStr `elem` expected
            then return $ Just (n,s)
            else getExp (n+1) r
    r <- case findExpressions input of
        []       -> return $ Nothing
        xs@((e, _, stats):_) -> [ Just ( (simplifyEta $ simplifyLets $ e, stats)
                                       , rs
                                       )
                                | rs <- getExp 0 xs
                                ]
    return $
      ( name
      , expected
      , r
      )

{-
checkBestResults :: ExferenceHeuristicsConfig
                 -> EnvDictionary
                 -> [ ( String
                      , [String]
                      , Maybe ( (Expression, ExferenceStats)
                                  -- ^ first result
                              , (Int, Expression, ExferenceStats)
                                  -- ^ best result
                              , Maybe (Int, ExferenceStats)
                                  -- ^ expected
                              )
                      )]
checkBestResults heuristics env = do
  (name, allowUnused, typeStr, expected) <- checkData
  let input = checkInput heuristics env typeStr allowUnused
  let getBest :: [(Expression, ExferenceStats)]
              -> (Int, Expression, ExferenceStats)
      getBest = maximumBy (comparing g) . zipWith (\a (b,c) -> (a,b,c)) [0..]
        where
          g (_,_,ExferenceStats _ f) = f
  let getExp :: Int
             -> [(Expression, ExferenceStats)]
             -> Maybe (Int, ExferenceStats)
      getExp _ [] = Nothing
      getExp n ((e,s):r) | show e `elem` expected = Just (n,s)
                         | otherwise              = getExp (n+1) r
  return $
    ( name
    , expected
    , case findExpressions input of
        [] -> Nothing
        xs@(x:_) -> Just (x, getBest xs, getExp 0 xs)
    )
-}

{-
checkBestResultsPar :: ExferenceHeuristicsConfig
                    -> EnvDictionary
                    -> [ IO ( String
                            , [String]
                            , Maybe ( (Expression, ExferenceStats)
                                        -- ^ first result
                                    , (Int, Expression, ExferenceStats)
                                        -- ^ best result
                                    , Maybe (Int, ExferenceStats)
                                        -- ^ expected
                                    )
                            )]
-}

{-
checkResults :: ExferenceHeuristicsConfig
             -> EnvDictionary
             -> [IO ( String -- name
                    , [String] -- expected
                    , Maybe Expression -- first
                    , Maybe Expression -- best
                    , Maybe (Int, ExferenceStats) -- expected was nth solution
                                                  -- and had these stats
                    , [(Expression, ExferenceStats)]
                    )]
checkResults heuristics (bindings, sEnv) = do
  (name, allowUnused, typeStr, expected) <- checkData
  let input = ExferenceInput
                (readConstrainedType sEnv typeStr)
                (filter (\(x,_,_) -> x/="join" && x/="liftA2") bindings)
                sEnv
                allowUnused
                131072
                (Just 131072)
                heuristics
  let r = findExpressionsPar input
  let finder :: Int
             -> [(Expression, ExferenceStats)]
             -> Maybe (Int, ExferenceStats)
      finder n [] = Nothing
      finder n ((e, s):r) | show e `elem` expected = Just (n, s)
                          | otherwise = finder (n+1) r
      bestFound = findSortNExpressions 100 input
  return $ (,,,,,)
         <$> return name
         <*> return expected
         <*> fmap fst <$> findOneExpressionPar input
         -- <*> return (fst <$> findOneExpression input)
         <*> return (fst <$> listToMaybe bestFound)
         <*> (finder 0 <$> r)
         <*> r
-}

exampleOutput :: ( m ~ MultiRWST r w s m0
                 , Monad m0
                 , Functor m0
                 , ContainsType QNameIndex s
                 )
              => ExferenceHeuristicsConfig
              -> EnvDictionary
              -> m [[(Expression, [HsConstraint], ExferenceStats)]]
exampleOutput heuristics (bindings, deconss, sEnv) =
  exampleInput `forM` \(_, allowUnused, patternM, s) -> do
    ty <- unsafeReadType (sClassEnv_tclasses sEnv) exampleDataTypes (IntMap.empty) s
    filteredBindings <- filterBindingsSimple ["join", "liftA2"] bindings
    qNameIndex <- mGet
    return $ takeFindSortNExpressions 10 10 $ ExferenceInput
                ty
                filteredBindings
                deconss
                sEnv
                allowUnused
                False
                8192
                patternM
                qNameIndex
                32768
                (Just 32768)
                heuristics

exampleInOut :: ( m ~ MultiRWST r w s m0
                , Monad m0
                , Functor m0
                , ContainsType QNameIndex s
                )
             => ExferenceHeuristicsConfig
             -> EnvDictionary
             -> m [( (String, Bool, Bool, String)
                   , [(Expression, [HsConstraint], ExferenceStats)]
                   )]
exampleInOut h env =
  zip exampleInput <$> exampleOutput h env

printAndStuff :: ContainsType QNameIndex s
              => ExferenceHeuristicsConfig
              -> EnvDictionary
              -> MultiRWST r w s IO ()
printAndStuff h env = exampleInOut h env >>= mapM_ f
  where
    f ((name, _, _, _), []) = lift $ putStrLn $ "no results for "++name++"!"
    f ((name, _, _, _), results) = mapM_ g results
      where
        g (expr, _, ExferenceStats n d m) = do
          str <- showExpression expr
          {-
          if doPf then do
            pf <- pointfree $ str
            putStrLn $ name ++ " = " ++ pf
                       ++ "    FROM    " ++ name ++ " = " ++ str
                       ++ " (depth " ++ show d ++ ", " ++ show n ++ " steps)"
           else
          -}
          lift $ putStrLn $ name ++ " = " ++ str
                            ++ " (depth "
                            ++ show d
                            ++ ", "
                            ++ show n
                            ++ " steps, "
                            ++ show m
                            ++ " max pqueue size)"

printStatistics :: ContainsType QNameIndex s
                => ExferenceHeuristicsConfig
                -> EnvDictionary
                -> MultiRWST r w s IO ()
printStatistics h env = exampleInOut h env >>= mapM_ f
  where
    f ((name, _, _, _), [])      = lift $ putStrLn $ printf "%10s: ---" name
    f ((name, _, _, _), results) =
      let (hd, avg, minV, maxV, n) = getStats results
      in lift $ putStrLn
              $ printf "%12s: head=%6d avg=%6d min=%6d max=%6d %s" name hd avg minV maxV
                                     (if n==6 then "" else " n = " ++ show n)
    getStats results =
      let steps = map (\(_, _, stats) -> exference_steps stats) results
      in ( head steps
         , sum steps `div` length steps
         , minimum steps
         , maximum steps
         , length steps
         )

printCheckExpectedResults :: forall r w s
                           . ( ContainsType QNameIndex s
                             , ContainsType TypeDeclMap r
                             )
                          => ExferenceHeuristicsConfig
                          -> EnvDictionary
                          -> MultiRWST r w s IO ()
printCheckExpectedResults h env = do
    qNameIndex <- mGet
    case () of { () -> do
    xs <- checkExpectedResults h env
    stats <- mapM helper xs
    lift $ putStrLn $ "total:     " ++ show (length stats)
    lift $ putStrLn $ "solutions: " ++ (show
                                       $ length
                                       $ catMaybes
                                       $ fst <$> stats)
    lift $ putStrLn $ "success:   " ++ ( show
                                       $ length
                                       $ filter id
                                       $ catMaybes
                                       $ uncurry (liftM2 (==)) <$> stats)
    lift $ putStrLn $ "rating any solutions: "
             ++ ( show
                $ foldr g (0, 0.0)
                $ fromMaybe (ExferenceStats 1000000 1000000 0) . fst <$> stats)
    lift $ putStrLn $ "rating good solutions: "
             ++ ( show
                $ foldr g (0, 0.0)
                $ fromMaybe (ExferenceStats 1000000 1000000 0) . snd <$> stats)
  where
    helper :: ( String -- ^ name
              , [String] -- ^ expected
              , Maybe ( (Expression, ExferenceStats) -- ^ first
                      , Maybe (Int, ExferenceStats)
                      ) -- ^ index and stats of expected
              )
           -> MultiRWST r w s IO (Maybe ExferenceStats, Maybe ExferenceStats)
    helper (name, _, Nothing) = do
      lift $ putStrLn $ printf "%-12s: no solutions found at all!" name
      return (Nothing, Nothing)
    helper (name, e, Just ((first,stats), Nothing)) = do
      lift $ putStrLn $ printf "%-12s: expected solution not found!" name
      firstStr <- showExpression first
      lift $ putStrLn $ "  first solution:       " ++ firstStr
      lift $ putStrLn $ "  first solution stats: " ++ show stats
      lift $ putStrLn $ "  expected solutions:   " ++ intercalate ", " e
      lift $ putStrLn $ "  " ++ show firstStr
      return (Just stats, Nothing)
    helper (name, _, Just (_, Just (0, stats))) = do
      lift $ putStrLn $ printf "%-12s: %s" name (show stats)
      return (Just stats, Just stats)
    helper (name, e, Just ((first, fstats), Just (n, stats))) = do
      lift $ putStrLn $ printf "%-12s: expected solution not first, but %d!" name n
      lift $ putStrLn $ "  first solution:     " ++ showExpressionPure qNameIndex first
      lift $ putStrLn $ "  expected solutions: " ++ intercalate " OR " e
      lift $ putStrLn $ "  first solution stats:    " ++ show fstats
      lift $ putStrLn $ "  expected solution stats: " ++ show stats
      lift $ putStrLn $ "  " ++ show (showExpressionPure qNameIndex first)
      return (Just fstats, Just stats)
    g :: ExferenceStats -> (Int,Float) -> (Int,Float)
    g (ExferenceStats a b _) (d,e) = (a+d,b+e)
  }

printMaxUsage :: ( ContainsType QNameIndex s )
              => ExferenceHeuristicsConfig
              -> EnvDictionary
              -> MultiRWST r w s IO ()
printMaxUsage h (bindings, deconss, sEnv) = sequence_ $ do
  (name, allowUnused, patternM, typeStr, _expected, hidden) <- checkData
  return $ do
    ty <- unsafeReadType (sClassEnv_tclasses sEnv) exampleDataTypes (IntMap.empty) typeStr
    filteredBindings <- filterBindingsSimple hidden bindings
    qNameIndex <- mGet
    let input = ExferenceInput
                  ty
                  filteredBindings
                  deconss
                  sEnv
                  allowUnused
                  False
                  8192
                  patternM
                  qNameIndex
                  16384
                  (Just 16384)
                  h
    let (stats, _, _) = last $ findExpressionsWithStats input
        highest = take 5 $ sortBy (flip $ comparing snd) $ M.toList stats
    lift $ putStrLn $ printf "%-12s: %s" name (show highest)

printSearchTree :: ( ContainsType QNameIndex s )
                => ExferenceHeuristicsConfig
                -> EnvDictionary
                -> MultiRWST r w s IO ()
printSearchTree h (bindings, deconss, sEnv) = sequence_ $ do
  (name, allowUnused, patternM, typeStr, _expected, hidden) <- checkData
  return $ do
    ty <- unsafeReadType (sClassEnv_tclasses sEnv) exampleDataTypes (IntMap.empty) typeStr
    filteredBindings <- filterBindingsSimple hidden bindings
    qNameIndex <- mGet
    let input = ExferenceInput
                  ty
                  filteredBindings
                  deconss
                  sEnv
                  allowUnused
                  False
                  8192
                  patternM
                  qNameIndex
                  256
                  (Just 256)
                  h
    let (_, tree, _) = last $ findExpressionsWithStats input
    let showf (total,processed,expression,_)
          = printf "%d (+%d): %s" processed
                                  (total-processed)
                                  (showExpressionPure qNameIndex expression)
    lift $ putStrLn
         $ name
    lift $ putStrLn
         $ drawTree
         $ fmap showf
         $ filterSearchTreeProcessedN 2
         $ tree
