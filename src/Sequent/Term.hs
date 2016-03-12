module Sequent.Term
    ( Variable
    , Predicate1
    , Predicate2
    , PredicateN
    , Term(..)
    , renameVariable
    , renamePredicate1
    , renamePredicate2
    , renamePredicateN ) where

import           Sequent.Env       (next)
import           Sequent.Introduce (Introduce, introduce)

import           Data.List         (intercalate)
import           Data.Maybe        (fromMaybe)

-- Wrapper around an integer, a variable can only be created using the
-- introduce function to avoid name collisions.
data Variable = Variable (Maybe String) Int

renameVariable :: String -> Variable -> Variable
renameVariable n (Variable _ x) = Variable (Just n) x

instance Eq Variable where
    (Variable _ x) == (Variable _ y) = x == y

instance Show Variable where
    show (Variable n x) = fromMaybe ("x" ++ show x) n

instance Introduce Variable where
  introduce = Variable Nothing <$> next

-- Variable is the name of the predicate
newtype Predicate1 = Predicate1 Variable deriving (Eq)

renamePredicate1 :: String -> Predicate1 -> Predicate1
renamePredicate1 n (Predicate1 v) = Predicate1 (renameVariable n v)

instance Show Predicate1 where
    show (Predicate1 (Variable n x)) = fromMaybe ("P" ++ show x) n

instance Introduce Predicate1 where
    introduce = Predicate1 <$> introduce

-- Variable is the name of the predicate
newtype Predicate2 = Predicate2 Variable deriving (Eq)

renamePredicate2 :: String -> Predicate2 -> Predicate2
renamePredicate2 n (Predicate2 v) = Predicate2 (renameVariable n v)

instance Show Predicate2 where
    show (Predicate2 (Variable n x)) = fromMaybe ("P" ++ show x) n

instance Introduce Predicate2 where
    introduce = Predicate2 <$> introduce

-- Variable is the name of the predicate
newtype PredicateN = PredicateN Variable deriving (Eq)

renamePredicateN :: String -> PredicateN -> PredicateN
renamePredicateN n (PredicateN v) = PredicateN (renameVariable n v)

instance Show PredicateN where
    show (PredicateN (Variable n x)) = fromMaybe ("P" ++ show x) n

-- A term is anything that can be introduced or passed to a quantifier
data Term = Var Variable
          | App1 Predicate1 Term
          | App2 Predicate2 Term Term
          | AppN PredicateN [Term]
          deriving (Eq)

instance Introduce Term where
  introduce = Var <$> introduce

instance Show Term where
    show (Var v) = show v
    show (App1 p t) = show p ++ "(" ++ show t ++ ")"
    show (App2 p t1 t2) = show p ++ "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
    show (AppN p ts) = show p ++ "(" ++ intercalate ", " (fmap show ts) ++ ")"
