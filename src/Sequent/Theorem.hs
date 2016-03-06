module Sequent.Theorem
    ( Theorem(..)
    , Judgment
    , (|-)
    ) where

import           Sequent.Env       (Env, evalEnv)
import           Sequent.Introduce (introduce)
import           Sequent.Term      (Term)

infix :->

-- TODO: add missing stuff
data Theorem
    = ForAll (Term -> Theorem)
    | ThereExists (Term -> Theorem)
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
eqTheorem (ThereExists f) (ThereExists f') = do
    x <- introduce
    eqTheorem (f x) (f' x)
eqTheorem _ _ = return False

showTheorem :: Theorem -> Env String
showTheorem (ForAll f) = do
    x <- introduce
    t <- showTheorem (f x)
    return ("forall " ++ show x ++ ". " ++ t)
showTheorem (ThereExists f) = do
    x <- introduce
    t <- showTheorem (f x)
    return ("there exists " ++ show x ++ ". " ++ t)
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
