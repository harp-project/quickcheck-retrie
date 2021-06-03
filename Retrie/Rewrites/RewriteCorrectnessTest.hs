-- Copyright (c) ELTE.
--
-- This source code is licensed under the MIT license.
--

{-# LANGUAGE OverloadedStrings, LambdaCase, TypeApplications #-}

module Retrie.Rewrites.RewriteCorrectnessTest where

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.QuickCheck.Poly
import Data.Char
import Control.Monad
import Control.Exception
import Data.List
import System.IO
import Language.Haskell.Ghcid
import Language.Haskell.Meta.Parse
import Language.Haskell.TH.Syntax
import Language.Haskell.Meta.Utils

splitOn :: Eq a => [a] -> [a] -> [[a]]
splitOn _ [] = [[]]
splitOn d l@(x:xs)
    | d `isPrefixOf` l = [] : splitOn d (dropList d l)
    | otherwise = (x : y) : ys
    where
        (y:ys) = splitOn d xs
        dropList [] lst = lst
        dropList (t:ts) (r:rs)
            | t == r = dropList ts rs

convertToFnType :: String -> String
convertToFnType varName = "(Fun _ " ++ varName ++ ")"

-- test = 2 == 3
-- test f xs ys = map (uncurry f) (zip xs ys) == zipWith f xs ys
-- test f xs ys = map f (zip xs ys) == zipWith (curry f) xs ys

-- tryTest :: Eq c => (b -> c) -> (a -> b) -> [a] -> IO ()
-- tryTest f g xs = quickCheck $ test f g xs

propertyLambda :: Fun (A,B) C -> [(A,B)] -> Property
propertyLambda (Fun _ f) xs = map f xs === uncurry (zipWith (curry f)) (unzip xs)

prop_map_zipWith :: Property
prop_map_zipWith = property propertyLambda 
-- forall f xs ys. map (uncurry f) (zip xs ys) = zipWith f xs ys

isRewritingAllowed :: String -> IO Bool
isRewritingAllowed adhocInput = do
    tryRunGhci <- (Right <$> startGhci "stack ghci --package QuickCheck" (Just ".") (const putStrLn))
      `catch` \e1 -> (Right <$> const (startGhci "cabal v2-repl --build-depends \"QuickCheck >= 2.14\"" (Just ".") (const putStrLn)) (e1 :: SomeException))
      `catch` \e -> (Right <$> const (startGhci "ghci" (Just ".") (const $ const $ return ())) (e :: SomeException))
      `catch` \e2 -> (Left <$> const (putStrLn "ERROR: Couldn't find either stack nor cabal nor ghci. Correctness checker cannot run.") (e2 :: SomeException))
    case tryRunGhci of
        Right (g,_) -> do
          let executeStatement = exec g
          importList <- filter (not . null) . map (head . splitOn " ") . splitOn ")" . concat <$> executeStatement ":show modules"
          executeStatement $ ":m + " ++ unwords (map ('*':) importList)
          executeStatement "import Test.QuickCheck"
          res <- unwords . words . concat <$> executeStatement (":t " ++ lambda)
          putStrLn res
          case splitOn ":: " res of
            [_,r] -> case parseType $ last $ splitOn "=>" r of
              Right t -> do 
                let varsWithTypes = zip variables $ map (map pp . argumentsOfType . typeVarToInteger) $ argumentsOfType t
                let length3 = [(parseExp a, length b) | (a, b@(_:_:_:_)) <- varsWithTypes]
                case all (\case ((Right _), _) -> True; _ -> False) length3 of
                  True -> do
                    let varExps = map (\(Right x,y) -> (x, y)) length3
                    case (parseExp lhs', parseExp rhs') of
                      (Right lhs, Right rhs) -> do
                        let (newLhs, newRhs) = foldr (\(exp,n) (l,r) -> (toCurriedExp n exp l, toCurriedExp n exp r)) (lhs,rhs) varExps
                        let newLambdaBody = '(' : filter (/= '\n') (pp newLhs) ++ ") === (" ++ filter (/= '\n') (pp newRhs) ++ ")"
                        lambdaRes <- executeStatement $ defineTestFunction varsWithTypes newLambdaBody
                        putStrLn "!!! LAMBDA !!!"
                        putStrLn $ unlines lambdaRes
                        testRes <- executeStatement "test"
                        (retText,retVal) <- return (case testRes of ['+':'+':'+':' ':'O':'K':_] -> ("Tests ran successfully.", True); x -> (unlines ("ERROR:" : x), False))
                        stopGhci g
                        putStrLn retText
                        return retVal
                      
                      (Right _, Left t)  -> stopGhci g >> putStrLn t >> putStrLn "ERROR: Couldn't parse the right-hand-side expression!" >> return False
                      (Left t, Right _)  -> stopGhci g >> putStrLn t >> putStrLn "ERROR: Couldn't parse the left-hand-side expression!" >> return False
                      (Left t1, Left t2) -> stopGhci g >> putStrLn t1 >> putStrLn ('\n':t2) >> putStrLn "\nERROR: Couldn't parse the either side of the expression!" >> return False
                  False -> stopGhci g >> putStrLn "ERROR: Couldn't parse all types!" >> return False
              Left t -> stopGhci g >> putStrLn t >> putStrLn "ERROR: Couldn't parse the type of input!" >> return False
            _ -> stopGhci g >> putStrLn "ERROR: Incorrect input format!" >> return False
        _ -> return False
    where
      typeVarToInteger :: Type -> Type
      typeVarToInteger (VarT _) = ConT (Name (OccName "Integer") NameS)
      typeVarToInteger (ForallT l cxt t) = ForallT l cxt (typeVarToInteger t)
      typeVarToInteger (AppT t1 t2) = AppT (typeVarToInteger t1) (typeVarToInteger t2)
      typeVarToInteger (SigT t k) = SigT (typeVarToInteger t) k
      typeVarToInteger (InfixT t1 n t2) = InfixT (typeVarToInteger t1) n (typeVarToInteger t2)
      typeVarToInteger (UInfixT t1 n t2) = UInfixT (typeVarToInteger t1) n (typeVarToInteger t2)
      typeVarToInteger (ParensT t) = ParensT (typeVarToInteger t)
      typeVarToInteger x = x

      argumentsOfType :: Type -> [Type]
      argumentsOfType (AppT (AppT ArrowT x) y) = x : argumentsOfType y
      argumentsOfType x = [x]

      defineTestFunction :: [(String, [String])] -> String -> String
      defineTestFunction varsWithTypeList lambdaBody = 
        "propertyFun :: " ++ intercalate " -> " (map (\(x,y) -> 
          case y of
            l@(_:_:_:_) -> "Fun (" ++ intercalate ", " (init l) ++ ") " ++ last l
            [l1,l2]     -> "Fun " ++ l1 ++ ' ':l2
            [l]         -> l) varsWithTypeList) ++ (if null varsWithTypeList then "" else " -> ") ++ "Property;\
        \propertyFun " ++ unwords (map (\(x,y) -> 
          case y of
            (_:_:_) -> convertToFnType x
            _       -> x) varsWithTypeList) ++ " = " ++ lambdaBody ++ ";\
        \test :: IO ();\
        \test = quickCheck $ withMaxSuccess 10000 propertyFun"
      
      breakOn :: ([a] -> Bool) -> [a] -> ([a],[a])
      breakOn _ [] = ([],[])
      breakOn f l@(x:xs)
        | f l = ([],l)
        | otherwise = (x:ys,zs)
        where
          (ys,zs) = breakOn f xs

      defineCurryN :: Int -> Exp
      defineCurryN n = let (Right t) = parseExp $ "(\\f " ++ unwords (map (('a':) . show) [1..n]) ++ " -> f (" ++ intercalate "," (map (('a':) . show) [1..n]) ++ "))" in t
      
      toCurriedExp :: Int -> Exp -> Exp -> Exp
      toCurriedExp n funExp exp
        | funExp == exp = ParensE (AppE (defineCurryN n) exp)
      toCurriedExp n funExp (AppE exp1 exp2) = AppE (toCurriedExp n funExp exp1) (toCurriedExp n funExp exp2)
      toCurriedExp n funExp (AppTypeE exp t) = AppTypeE (toCurriedExp n funExp exp) t
      toCurriedExp n funExp (InfixE maybeExp1 exp2 maybeExp3) = InfixE (toCurriedExp n funExp <$> maybeExp1) (toCurriedExp n funExp exp2) (toCurriedExp n funExp <$> maybeExp3)
      toCurriedExp n funExp (UInfixE exp1 exp2 exp3) = UInfixE (toCurriedExp n funExp exp1) (toCurriedExp n funExp exp2) (toCurriedExp n funExp exp3)
      toCurriedExp n funExp (ParensE exp) = ParensE (toCurriedExp n funExp exp)
      toCurriedExp n funExp (LamE pat exp) = LamE pat (toCurriedExp n funExp exp)
      toCurriedExp n funExp (TupE expList) = TupE (map (toCurriedExp n funExp) expList)
      toCurriedExp n funExp (UnboxedTupE expList) = UnboxedTupE (map (toCurriedExp n funExp) expList)
      toCurriedExp n funExp (UnboxedSumE exp sumAlt arity) = UnboxedSumE (toCurriedExp n funExp exp) sumAlt arity
      toCurriedExp n funExp (CondE exp1 exp2 exp3) = CondE (toCurriedExp n funExp exp1) (toCurriedExp n funExp exp2) (toCurriedExp n funExp exp3)
      toCurriedExp n funExp (MultiIfE guardExpList) = MultiIfE (map (\(g,exp) -> (g, toCurriedExp n funExp exp)) guardExpList)
      toCurriedExp n funExp (LetE decList exp) = LetE decList (toCurriedExp n funExp exp)
      toCurriedExp n funExp (CaseE exp matchList) = CaseE (toCurriedExp n funExp exp) (map (\(Match p body decList) -> Match p (case body of 
        GuardedB guardExpList -> GuardedB (map (\(g,exp) -> (g,toCurriedExp n funExp exp)) guardExpList)
        NormalB exp -> NormalB (toCurriedExp n funExp exp)) decList) matchList)
      toCurriedExp n funExp (ListE expList) = ListE (map (toCurriedExp n funExp) expList)
      toCurriedExp n funExp (SigE exp t) = SigE (toCurriedExp n funExp exp) t
      toCurriedExp n funExp (RecUpdE exp fieldExpList) = RecUpdE (toCurriedExp n funExp exp) (map (\(name,exp) -> (name,toCurriedExp n funExp exp)) fieldExpList)
      toCurriedExp n funExp (StaticE exp) = StaticE (toCurriedExp n funExp exp)
      toCurriedExp _ _ exp = exp
      
      (forallPart, refactorRule) = if "forall" `isPrefixOf` (dropWhile isSpace adhocInput) 
        then (\(a,b) -> (a, dropWhile isSpace $ drop 1 b)) . break (== '.') $ adhocInput 
        else ([],adhocInput)
      (lhs', rhs') = (\(a,b) -> ('(' : a ++ ")", '(' : dropWhile isSpace (drop 1 b) ++ ")")) $ break (== '=') refactorRule
      variables = drop 1 $ words forallPart
      lambdaBody = lhs' ++ " === " ++ rhs'
      lambda = case variables of 
        [] -> lambdaBody
        _  -> '\\' : unwords variables ++ " -> " ++ lambdaBody