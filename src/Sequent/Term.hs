module Sequent.Term
    ( Variable
    , Predicate1
    , Predicate2
    , PredicateN
    , Term(..) ) where

import           Sequent.Env       (next)
import           Sequent.Introduce (Introduce, introduce)

import           Data.List         (intercalate)

-- Wrapper around an integer, a variable can only be created using the
-- introduce function to avoid name collisions.
newtype Variable = Variable Int deriving (Eq)

instance Show Variable where
    show (Variable x) = "x" ++ show x

instance Introduce Variable where
  introduce = Variable <$> next

-- Variable is the name of the predicate
newtype Predicate1 = Predicate1 Variable deriving (Eq)

instance Show Predicate1 where
    show (Predicate1 (Variable x)) = "P" ++ show x

instance Introduce Predicate1 where
    introduce = Predicate1 <$> introduce

-- Variable is the name of the predicate
newtype Predicate2 = Predicate2 Variable deriving (Eq)

instance Show Predicate2 where
    show (Predicate2 (Variable x)) = "P" ++ show x

instance Introduce Predicate2 where
    introduce = Predicate2 <$> introduce

-- Variable is the name of the predicate
newtype PredicateN = PredicateN Variable deriving (Eq)

instance Show PredicateN where
    show (PredicateN (Variable x)) = "P" ++ show x

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
