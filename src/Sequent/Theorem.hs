module Sequent.Theorem
    ( TheoremAtom(..)
    , Theorem
    , (|-)
    ) where

import           Sequent.Env (Env, Variable, evalEnv, fresh)

data TheoremAtom
    = ForAll (Variable -> TheoremAtom)
    | Or TheoremAtom TheoremAtom
    | Not TheoremAtom
    | Var Variable

instance Eq TheoremAtom where
  a == b = evalEnv (eqTheoremAtom a b)

instance Show TheoremAtom where
  show = evalEnv . showTheoremAtom

-- TODO: maybe wrap in a newtype? (or a record?)
type Theorem = ([TheoremAtom], [TheoremAtom])

-- TODO fix infix
infixr |-
(|-) = (,)

-- to show or test equality of two theorems we must be able to replace
-- quantifiers with contrete variables in order to eliminate functions
-- in our haskell representation of the theorem and explore the subtheorem

eqTheoremAtom :: TheoremAtom -> TheoremAtom -> Env Bool
eqTheoremAtom (Var x) (Var y) = return (x == y)
eqTheoremAtom (Or l r) (Or l' r') = return (l == l' && r == r')
eqTheoremAtom (Not t) (Not t') = return (t == t')
eqTheoremAtom (ForAll f) (ForAll f') = do
  x <- fresh
  eqTheoremAtom (f x) (f' x)
eqTheoremAtom _ _ = return False

showTheoremAtom :: TheoremAtom -> Env String
showTheoremAtom (ForAll f) = do
    x <- fresh
    t <- showTheoremAtom (f x)
    return ("forall " ++ show x ++ ". " ++ t)
showTheoremAtom (Or l r) = do
    sl <- showTheoremAtom l
    sr <- showTheoremAtom r
    return (sl ++ " \\/ " ++ sr)
showTheoremAtom (Not t) = do
    st <- showTheoremAtom t
    return ("!(" ++ st ++ ")")
showTheoremAtom (Var s) = return (show s)
