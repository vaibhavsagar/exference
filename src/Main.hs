{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}

module Main
  ( main
  )
where



import Language.Haskell.Exference
import Language.Haskell.Exference.ExpressionToHaskellSrc
import Language.Haskell.Exference.BindingsFromHaskellSrc
import Language.Haskell.Exference.ContextFromHaskellSrc
import Language.Haskell.Exference.TypeFromHaskellSrc
import Language.Haskell.Exference.FunctionBinding
import Language.Haskell.Exference.ContextParser

import Language.Haskell.Exference.ConstrainedType
import Language.Haskell.Exference.SimpleDict
import Language.Haskell.Exference.TypeClasses
import Language.Haskell.Exference.Expression
import Language.Haskell.Exference.ExferenceStats

import Control.DeepSeq

import System.Process

import Control.Applicative ( (<$>), (<*>) )
import Control.Arrow ( second, (***) )
import Control.Monad ( when, forM_, guard, forM, mplus, mzero )
import Data.List ( sortBy, find )
import Data.Ord ( comparing )
import Text.Printf
import Data.Maybe ( listToMaybe, fromMaybe, maybeToList )
import Data.Either ( lefts, rights )
import Control.Monad.Writer.Strict

import Language.Haskell.Exts.Syntax ( Module(..), Decl(..), ModuleName(..) )
import Language.Haskell.Exts.Parser ( parseModuleWithMode
                                    , parseModule
                                    , ParseResult (..)
                                    , ParseMode (..)
                                    , defaultParseMode )
import Language.Haskell.Exts.Extension ( Language (..)
                                       , Extension (..)
                                       , KnownExtension (..) )

import Data.PPrint

import Control.Arrow ( first )

import MainTest

import Debug.Hood.Observe





testDictRatings :: [(String, Float)]
testDictRatings =
  [ (,) "maybe"    0.0
  , (,) "either"   0.0
  , (,) "curry"    0.0
  , (,) "uncurry"  0.0
  --, (,) "compare"  0.0
  --, (,) "minBound" 0.0
  --, (,) "maxBound" 0.0
  , (,) "fmap"     0.0
  -- , (,) "pure"     0.0
  -- , (,) "(<*>)"    0.0
  , (,) "(>>=)"    0.0
  , (,) "mapM"     0.0
  , (,) "sequence" 0.0
  , (,) "foldl"    0.0
  , (,) "foldr"    0.0
  , (,) "concat"   0.0
  , (,) "zip"      0.0
  , (,) "zip3"     0.0
  , (,) "zipWith"  0.0
  , (,) "unzip"    0.0
  , (,) "unzip3"   0.0
  , (,) "repeat"   0.0
  , (,) "Just"     0.0
  --, (,) "(&&)"       0.0
  --, (,) "(||)"       0.0
  ]






testBaseInput :: [(Bool, String)]
testBaseInput = [ (,) True  "GHCEnum"
                , (,) True  "GHCReal"
                , (,) True  "GHCShow"
                , (,) False "ControlMonad"
                , (,) False "DataEither"
                , (,) False "DataList"
                , (,) False "DataMaybe"
                , (,) False "DataTuple"
                , (,) False "DataOrd"
                , (,) False "GHCArr"
                , (,) False "GHCBase"
                , (,) False "GHCFloat"
                , (,) False "GHCList"
                , (,) False "GHCNum"
                , (,) False "GHCST"
                , (,) False "SystemIOError"
                , (,) False "SystemIO"
                , (,) False "TextRead"
                ]

testBaseInput' :: [(ParseMode, String)]
testBaseInput' = map h testBaseInput
  where
    h (shouldBangPattern, s) =
      let exts1 = (if shouldBangPattern then (BangPatterns:) else id)
                  [ UnboxedTuples
                  , TypeOperators
                  , MagicHash
                  , NPlusKPatterns
                  , ExplicitForAll
                  , ExistentialQuantification
                  , TypeFamilies
                  , PolyKinds
                  , DataKinds ]
          exts2 = map EnableExtension exts1
          mode = ParseMode (s++".hs")
                           Haskell2010
                           exts2
                           False
                           False
                           Nothing
          fname = "./BaseContext/preprocessed/"++s++".hs"
      in (mode, fname)

main = runO $ do
  --printAndStuff
  --printChecks
  --printStatistics
  let
    tryParse :: Bool -> String -> IO ()
    tryParse shouldBangPattern s = do
      content <- readFile $ "./BaseContext/preprocessed/"++s++".hs"
      let exts1 = (if shouldBangPattern then (BangPatterns:) else id)
                  [ UnboxedTuples
                  , TypeOperators
                  , MagicHash
                  , NPlusKPatterns
                  , ExplicitForAll
                  , ExistentialQuantification
                  , TypeFamilies
                  , PolyKinds
                  , DataKinds ]
          exts2 = map EnableExtension exts1
      case parseModuleWithMode (ParseMode (s++".hs")
                                          Haskell2010
                                          exts2
                                          False
                                          False
                                          Nothing
                               )
                               content of
        f@(ParseFailed _ _) -> do
          print f
        ParseOk mod -> do
          putStrLn s
          --mapM_ putStrLn $ map (either id show)
          --               $ getBindings defaultContext mod
          --mapM_ putStrLn $ map (either id show)
          --               $ getDataConss mod
          --mapM_ putStrLn $ map (either id show)
          --               $ getClassMethods defaultContext mod
  --((eSignatures, StaticContext clss insts), messages) <- runWriter <$> parseExternal testBaseInput'
  ((eSignatures, StaticContext clss insts), messages)
    <- runWriter
    <$> contextFromModuleSimple "ExferenceDict.hs"
  mapM_ print $ messages
  -- mapM_ print $ clss
  mapM_ print $ insts
  mapM_ print $ eSignatures
  -- print $ compileDict testDictRatings $ eSignatures
  -- print $ parseConstrainedType defaultContext $ "(Show a) => [a] -> String"
  -- print $ inflateConstraints a b
  {-
  print $ constraintMatches testDynContext (badReadVar "y") (read "x")
  print $ constraintMatches testDynContext (badReadVar "x") (read "y")
  print $ constraintMatches testDynContext (badReadVar "w") (read "MyFoo")
  print $ constraintMatches testDynContext (badReadVar "w") (read "MyBar")
  print $ constraintMatches testDynContext (badReadVar "y") (read "MyFoo")
  print $ isProvable testDynContext [Constraint c_applicative [read "y"]]
  -}
  -- putStrLn $ show n ++ " total steps"
  {-
  let t :: HsType
      t = read "m a->( ( a->m b)->( m b))"
  print $ t
  -}

pointfree :: String -> IO String
pointfree s = (!!1) <$> lines <$> readProcess "pointfree" ["--verbose", s] ""

pointful :: String -> IO String
pointful s = (!!0) <$> lines <$> readProcess "pointful" [s] ""
