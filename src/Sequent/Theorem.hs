module Sequent.Theorem
    ( Theorem(..)
    , Judgment
    , (|-)
    ) where

import           Sequent.Env (Env, Variable, evalEnv, fresh)

-- TODO: add existential quantifier and and
data Theorem
    = ForAll (Variable -> Theorem)
    | Or Theorem Theorem
    | Not Theorem
    | Var Variable

instance Eq Theorem where
  a == b = evalEnv (eqTheorem a b)

instance Show Theorem where
  show = evalEnv . showTheorem

-- TODO: maybe wrap in a newtype? (or a record?) with monoid instance
type Judgment = ([Theorem], [Theorem])

-- TODO fix infix
infixr |-
(|-) = (,)

-- to show or test equality of two theorems we must be able to replace
-- quantifiers with contrete variables in order to eliminate functions
-- in our haskell representation of the theorem and explore the subtheorem

eqTheorem :: Theorem -> Theorem -> Env Bool
eqTheorem (Var x) (Var y) = return (x == y)
eqTheorem (Or l r) (Or l' r') = (&&) <$> eqTheorem l l' <*> eqTheorem r r'
eqTheorem (Not t) (Not t') = eqTheorem t t'
eqTheorem (ForAll f) (ForAll f') = do
  x <- fresh
  eqTheorem (f x) (f' x)
eqTheorem _ _ = return False

showTheorem :: Theorem -> Env String
showTheorem (ForAll f) = do
    x <- fresh
    t <- showTheorem (f x)
    return ("forall " ++ show x ++ ". " ++ t)
showTheorem (Or l r) = do
    sl <- showTheorem l
    sr <- showTheorem r
    return (sl ++ " \\/ " ++ sr)
showTheorem (Not t) = do
    st <- showTheorem t
    return ("!(" ++ st ++ ")")
showTheorem (Var s) = return (show s)
