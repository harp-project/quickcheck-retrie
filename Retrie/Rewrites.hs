{-# LANGUAGE RecordWildCards #-}
-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE OverloadedStrings #-}
module Retrie.Rewrites
  ( RewriteSpec(..)
  , QualifiedName
  , parseRewriteSpecs
  , parseQualified
  , parseAdhocs
  ) where

import Control.Exception
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Text as Text
import Data.Traversable
import System.FilePath

import Retrie.CPP
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GHC
import Retrie.Rewrites.Function
import Retrie.Rewrites.Patterns
import Retrie.Rewrites.Rules
import Retrie.Rewrites.Types
import Retrie.Rewrites.RewriteCorrectnessTest
import Retrie.Types
import Retrie.Universe

-- | A qualified name. (e.g. @"Module.Name.functionName"@)
type QualifiedName = String

-- | Possible ways to specify rewrites to 'parseRewrites'.
data RewriteSpec
  = Adhoc String
    -- ^ Equation in RULES-format. (e.g. @"forall x. succ (pred x) = x"@)
    -- Will be applied left-to-right.
  | AdhocWithTesting String
    -- ^ Equation in RULES-format. (e.g. @"forall x. succ (pred x) = x"@)
    -- Will be applied left-to-right.
    -- Will be tested whether lhs and rhs are semantically the same using QuickCheck.
  | AdhocPattern String
    -- ^ Equation in pattern-synonym format, _without_ the keyword 'pattern'.
  | AdhocType String
    -- ^ Equation in type-synonym format, _without_ the keyword 'type'.
  | Fold QualifiedName
    -- ^ Fold a function definition. The inverse of unfolding/inlining.
    -- Replaces instances of the function body with calls to the function.
  | RuleBackward QualifiedName
    -- ^ Apply a GHC RULE right-to-left.
  | RuleForward QualifiedName
    -- ^ Apply a GHC RULE left-to-right.
  | TypeBackward QualifiedName
    -- ^ Apply a type synonym right-to-left.
  | TypeForward QualifiedName
    -- ^ Apply a type synonym left-to-right.
  | Unfold QualifiedName
    -- ^ Unfold, or inline, a function definition.
  | PatternForward QualifiedName
    -- ^ Unfold a pattern synonym
  | PatternBackward QualifiedName
    -- ^ Fold a pattern synonym, replacing instances of the rhs with the synonym


data ClassifiedRewrites = ClassifiedRewrites
  { adhocRules :: [String]
  , adhocPatterns :: [String]
  , adhocTypes :: [String]
  , fileBased :: [(FilePath, [(FileBasedTy,[(FastString, Direction)])])]
  }

instance Monoid ClassifiedRewrites where
  mempty = ClassifiedRewrites [] [] [] []

instance Semigroup ClassifiedRewrites where
  ClassifiedRewrites a b c d <> ClassifiedRewrites a' b' c' d' =
    ClassifiedRewrites (a <> a') (b <> b') (c <> c') (d <> d')

parseRewriteSpecs
  :: (FilePath -> IO (CPP AnnotatedModule))
  -> FixityEnv
  -> [RewriteSpec]
  -> IO [Rewrite Universe]
parseRewriteSpecs parser fixityEnv specs = do
  ClassifiedRewrites{..} <- mconcat <$> sequence
    [ case spec of
        Adhoc rule -> return mempty{adhocRules = [rule]}
        AdhocWithTesting rule -> do
          writeFile "something2.txt" "isRewriting is Running"
          isAllowed <- isRewritingAllowed rule
          if isAllowed 
            then return $ mempty{adhocRules = [rule]} 
            else putStrLn "lhs and rhs are semantically not the same! Rewriting did not take place!" >> return mempty{adhocRules = []}
        AdhocPattern pSyn -> return mempty{adhocPatterns = [pSyn]}
        AdhocType tySyn -> return mempty{adhocTypes = [tySyn]}
        Fold name -> mkFileBased FoldUnfold RightToLeft name
        RuleBackward name -> mkFileBased Rule RightToLeft name
        RuleForward name -> mkFileBased Rule LeftToRight name
        TypeBackward name -> mkFileBased Type RightToLeft name
        TypeForward name -> mkFileBased Type LeftToRight name
        PatternBackward name -> mkFileBased Pattern RightToLeft name
        PatternForward name -> mkFileBased Pattern LeftToRight name
        Unfold name -> mkFileBased FoldUnfold LeftToRight name
    | spec <- specs
    ]
  fbRewrites <- parseFileBased parser fileBased
  adhocExpressionRewrites <- parseAdhocs fixityEnv adhocRules
  adhocTypeRewrites <- parseAdhocTypes fixityEnv adhocTypes
  adhocPatternRewrites <- parseAdhocPatterns fixityEnv adhocPatterns
  return $
    fbRewrites ++
    adhocExpressionRewrites ++
    adhocTypeRewrites ++
    adhocPatternRewrites
  where
    mkFileBased ty dir name =
      case parseQualified name of
        Left err -> throwIO $ ErrorCall $ "parseRewriteSpecs: " ++ err
        Right (fp, fs) -> return mempty{fileBased = [(fp, [(ty, [(fs, dir)])])]}

data FileBasedTy = FoldUnfold | Rule | Type | Pattern
  deriving (Eq, Ord)

parseFileBased
  :: (FilePath -> IO (CPP AnnotatedModule))
  -> [(FilePath, [(FileBasedTy, [(FastString, Direction)])])]
  -> IO [Rewrite Universe]
parseFileBased _ [] = return []
parseFileBased parser specs = concat <$> mapM (uncurry goFile) (gather specs)
  where
    gather :: Ord a => [(a,[b])] -> [(a,[b])]
    gather = Map.toList . Map.fromListWith (++)

    goFile
      :: FilePath
      -> [(FileBasedTy, [(FastString, Direction)])]
      -> IO [Rewrite Universe]
    goFile fp rules = do
      cpp <- parser fp
      concat <$> mapM (uncurry $ constructRewrites cpp) (gather rules)

parseAdhocs :: FixityEnv -> [String] -> IO [Rewrite Universe]
parseAdhocs _ [] = return []
parseAdhocs fixities adhocs = do
  cpp <-
    parseCPP (parseContent fixities "parseAdhocs") (Text.unlines adhocRules)
  constructRewrites cpp Rule adhocSpecs
  where
    -- In search mode, there is no need to specify a right-hand side, but we
    -- need one to parse as a RULE, so add it if necessary.
    addRHS s
      | '=' `elem` s = s
      | otherwise = s ++ " = undefined"
    (adhocSpecs, adhocRules) = unzip
      [ ( (mkFastString nm, LeftToRight)
        , "{-# RULES \"" <> Text.pack nm <> "\" " <> Text.pack s <> " #-}"
        )
      | (i,s) <- zip [1..] $ map addRHS adhocs
      , let nm = "adhoc" ++ show (i::Int)
      ]

parseAdhocTypes :: FixityEnv -> [String] -> IO [Rewrite Universe]
parseAdhocTypes _ [] = return []
parseAdhocTypes fixities tySyns = do
  print adhocTySyns
  cpp <-
    parseCPP (parseContent fixities "parseAdhocTypes") (Text.unlines adhocTySyns)
  constructRewrites cpp Type adhocSpecs
  where
    (adhocSpecs, adhocTySyns) = unzip
      [ ( (mkFastString nm, LeftToRight), "type " <> Text.pack s)
      | s <- tySyns
      , Just nm <- [listToMaybe $ words s]
      ]

parseAdhocPatterns :: FixityEnv -> [String] -> IO [Rewrite Universe]
parseAdhocPatterns _ [] = return []
parseAdhocPatterns fixities patSyns = do
  cpp <-
    parseCPP (parseContent fixities "parseAdhocPatterns")
             (Text.unlines $ pragma : adhocPatSyns)
  constructRewrites cpp Pattern adhocSpecs
  where
    pragma = "{-# LANGUAGE PatternSynonyms #-}"
    (adhocSpecs, adhocPatSyns) = unzip
      [ ( (mkFastString nm, LeftToRight), "pattern " <> Text.pack s)
      | s <- patSyns
      , Just nm <- [listToMaybe $ words s]
      ]

constructRewrites
  :: CPP AnnotatedModule
  -> FileBasedTy
  -> [(FastString, Direction)]
  -> IO [Rewrite Universe]
constructRewrites cpp ty specs = do
  cppM <- traverse (tyBuilder ty specs) cpp
  let
    names = nonDetEltsUniqSet $ mkUniqSet $ map fst specs

    nameOf FoldUnfold = "definition"
    nameOf Rule = "rule"
    nameOf Type = "type synonym"
    nameOf Pattern = "pattern synonym"

    m = foldr (plusUFM_C (++)) emptyUFM cppM

  fmap concat $ forM names $ \fs ->
    case lookupUFM m fs of
      Nothing ->
        fail $ "could not find " ++ nameOf ty ++ " named " ++ unpackFS fs
      Just rrs -> return rrs

tyBuilder
  :: FileBasedTy
  -> [(FastString, Direction)]
  -> AnnotatedModule
  -> IO (UniqFM [Rewrite Universe])
tyBuilder FoldUnfold specs am = promote <$> dfnsToRewrites specs am
tyBuilder Rule specs am = promote <$> rulesToRewrites specs am
tyBuilder Type specs am = promote <$> typeSynonymsToRewrites specs am
tyBuilder Pattern specs am = patternSynonymsToRewrites specs am

promote :: Matchable a => UniqFM [Rewrite a] -> UniqFM [Rewrite Universe]
promote = fmap (map toURewrite)

parseQualified :: String -> Either String (FilePath, FastString)
parseQualified [] = Left "qualified name is empty"
parseQualified fqName =
  case span isHsSymbol reversed of
    (_,[]) -> mkError "unqualified operator name"
    ([],_) ->
      case span (/='.') reversed of
        (_,[]) -> mkError "unqualified function name"
        (rname,_:rmod) -> mkResult (reverse rmod) (reverse rname)
    (rop,rmod) ->
      case reverse rop of
        '.':op -> mkResult (reverse rmod) op
        _ -> mkError "malformed qualified operator"
  where
    reversed = reverse fqName
    mkError str = Left $ str ++ ": " ++ fqName
    mkResult moduleNameStr occNameStr = Right
      -- 'moduleNameSlashes' gives us system-dependent path separator
      ( moduleNameSlashes (mkModuleName moduleNameStr) <.> "hs"
      , mkFastString occNameStr
      )

isHsSymbol :: Char -> Bool
isHsSymbol = (`elem` symbols)
  -- see https://www.haskell.org/onlinereport/lexemes.html
  where
    symbols :: String
    symbols = "!#$%&*+./<=>?@\\^|-~"
