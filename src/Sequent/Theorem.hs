module Sequent.Theorem
    ( Theorem(..)
    , Judgment
    , Predicate1
    , Predicate2
    , PredicateN
    , Term(..)
    , (|-)
    ) where

import           Data.List         (intercalate)
import           Sequent.Env       (Env, Variable (..), evalEnv)
import           Sequent.Introduce (Introduce, introduce)

infix :->

-- Variable is the name of the predicate
newtype Predicate1 = Predicate1 Variable deriving (Eq)
newtype Predicate2 = Predicate2 Variable deriving (Eq)
newtype PredicateN = PredicateN Variable deriving (Eq)

instance Show Predicate1 where
    show (Predicate1 (Variable x)) = "P" ++ show x

instance Show Predicate2 where
    show (Predicate2 (Variable x)) = "P" ++ show x

instance Show PredicateN where
    show (PredicateN (Variable x)) = "P" ++ show x

instance Introduce Predicate1 where
    introduce = Predicate1 <$> introduce

instance Introduce Predicate2 where
    introduce = Predicate2 <$> introduce

instance Introduce Term where
    introduce = Var <$> introduce

data Term = Var Variable
          | App1 Predicate1 Term
          | App2 Predicate2 (Term, Term)
          | AppN PredicateN [Term]
          deriving (Eq)

instance Show Term where
    show (Var v) = show v
    show (App1 p t) = show p ++ "(" ++ show t ++ ")"
    show (App2 p ts) = show p ++ show ts
    show (AppN p ts) = show p ++ "(" ++ intercalate ", " (fmap show ts) ++ ")"

-- TODO: add missing stuff
data Theorem
    = ForAll (Term -> Theorem)
    | Or Theorem Theorem
    | And Theorem Theorem
    | Not Theorem
    | Theorem :-> Theorem
    | TTerm Term

instance Eq Theorem where
  a == b = evalEnv (eqTheorem a b)

instance Show Theorem where
  show = evalEnv . showTheorem

-- TODO: maybe wrap in a newtype? (or a record?) with monoid instance
type Judgment = ([Theorem], [Theorem])

-- TODO fix infix
infixr |-

(|-) :: [Theorem] -> [Theorem] -> Judgment
(|-) = (,)

-- to show or test equality of two theorems we must be able to replace
-- quantifiers with contrete variables in order to eliminate functions
-- in our haskell representation of the theorem and explore the subtheorem

eqTheorem :: Theorem -> Theorem -> Env Bool
eqTheorem (TTerm x) (TTerm y) = return (x == y)
eqTheorem (Or l r) (Or l' r') = (&&) <$> eqTheorem l l' <*> eqTheorem r r'
eqTheorem (And l r) (And l' r') = (&&) <$> eqTheorem l l' <*> eqTheorem r r'
eqTheorem (Not t) (Not t') = eqTheorem t t'
eqTheorem (l :-> r) (l' :-> r') = (&&) <$> eqTheorem l l' <*> eqTheorem r r'
eqTheorem (ForAll f) (ForAll f') = do
  x <- introduce
  eqTheorem (f x) (f' x)
eqTheorem _ _ = return False

showTheorem :: Theorem -> Env String
showTheorem (ForAll f) = do
    x <- introduce
    t <- showTheorem (f x)
    return ("forall " ++ show x ++ ". " ++ t)
showTheorem (Or l r) = do
    sl <- showTheorem l
    sr <- showTheorem r
    return (sl ++ " \\/ " ++ sr)
showTheorem (And l r) = do
    sl <- showTheorem l
    sr <- showTheorem r
    return (sl ++ "/\\ " ++ sr)
showTheorem (Not t) = do
    st <- showTheorem t
    return ("!(" ++ st ++ ")")
showTheorem (l :-> r) = do
    sl <- showTheorem l
    sr <- showTheorem r
    return (sl ++ " -> " ++ sr)
showTheorem (TTerm t) = return (show t)
