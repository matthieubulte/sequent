module Sequent.Theorem
    ( Theorem(..)
    , Judgment
    , (|-)
    ) where

import           Sequent.Env (Env, Variable, evalEnv, fresh)

infix :->

-- TODO: add missing stuff
data Theorem
    = ForAll (Variable -> Theorem)
    | Or Theorem Theorem
    | And Theorem Theorem
    | Not Theorem
    | Theorem :-> Theorem
    | Var Variable
    | Pred1 Variable Variable             -- first variable is the predicate name
    | Pred2 Variable (Variable, Variable) -- first variable is the predicate name
    | PredN Variable [Variable]           -- first variable is the predicate name

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
eqTheorem (Pred1 p x) (Pred1 p' x') = return (p == p' && x == x')
eqTheorem (Pred2 p xs) (Pred2 p' xs') = return (p == p' && xs == xs')
eqTheorem (PredN p xs) (PredN p' xs') = return (p == p' && xs == xs')
eqTheorem (Or l r) (Or l' r') = (&&) <$> eqTheorem l l' <*> eqTheorem r r'
eqTheorem (And l r) (And l' r') = (&&) <$> eqTheorem l l' <*> eqTheorem r r'
eqTheorem (Not t) (Not t') = eqTheorem t t'
eqTheorem (l :-> r) (l' :-> r') = (&&) <$> eqTheorem l l' <*> eqTheorem r r'
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
showTheorem (Var s) = return (show s)
showTheorem (Pred1 p x) = return (show p ++ show x)
showTheorem (Pred2 p xs) = return (show p ++ show xs)
showTheorem (PredN p xs) = return (show p ++ show xs)
