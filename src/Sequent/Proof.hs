module Sequent.Proof
    ( Proof(..)
    ) where

import           Control.Arrow ((&&&))
import           Control.Monad (zipWithM)
import           Data.List     (intercalate)

import           Sequent.Env   (Env, Variable, evalEnv, fresh)

data Proof
  = ContractionSuccedent Proof
  | ForAllSuccedent (Variable -> Proof)
  | ForAllAntecedent Variable Proof
  | OrElimLeftSuccedent Proof
  | OrElimRightSuccedent Proof
  | NegationSuccedent Proof
  | NegationAntecedent Proof
  | OrElimAntecedent Proof Proof
  | AndElimSuccedent Proof Proof
  | AndElimLeftAntecedent Proof
  | AndElimRightAntecedent Proof
  | PermuteSuccedent Proof
  | PermuteAntecedent Proof
  | Axiom

instance Eq Proof where
    a == b = evalEnv (eqProofs a b)

instance Show Proof where
    show = evalEnv . showProof

-- to show or test equality of two theorems we must be able to replace
-- quantifiers with contrete variables in order to eliminate functions
-- in our haskell representation of the theorem and explore the subtheorem

eqProofs :: Proof -> Proof -> Env Bool
eqProofs Axiom Axiom = return True
eqProofs (ContractionSuccedent s)   (ContractionSuccedent s')   = eqProofs s s'
eqProofs (OrElimLeftSuccedent s)    (OrElimLeftSuccedent s')    = eqProofs s s'
eqProofs (OrElimRightSuccedent s)   (OrElimRightSuccedent s')   = eqProofs s s'
eqProofs (NegationSuccedent s)      (NegationSuccedent s')      = eqProofs s s'
eqProofs (NegationAntecedent s)     (NegationAntecedent s')     = eqProofs s s'
eqProofs (AndElimLeftAntecedent s)  (AndElimLeftAntecedent s')  = eqProofs s s'
eqProofs (AndElimRightAntecedent s) (AndElimRightAntecedent s') = eqProofs s s'
eqProofs (PermuteSuccedent s)       (PermuteSuccedent s')       = eqProofs s s'
eqProofs (PermuteAntecedent s)      (PermuteAntecedent s')      = eqProofs s s'
eqProofs (ForAllAntecedent a s)     (ForAllAntecedent a' s')    =
    (a == a' &&) <$> eqProofs s s'
eqProofs (ForAllSuccedent f) (ForAllSuccedent f') =
    fresh >>= uncurry eqProofs . (f &&& f')
eqProofs (OrElimAntecedent l r) (OrElimAntecedent l' r') =
    (&&) <$> eqProofs l l' <*> eqProofs r r'
eqProofs (AndElimSuccedent l r) (AndElimSuccedent l' r') =
    (&&) <$> eqProofs l l' <*> eqProofs r r'
eqProofs _ _ = return False

thenShow :: String -> Proof -> Env String
thenShow s p = ((s ++ "\n") ++) <$> showProof p

showProof :: Proof -> Env String
showProof Axiom                      = return "Axiom"
showProof (ContractionSuccedent s)   = "ContractionSuccedent"          `thenShow` s
showProof (ForAllAntecedent a s)     = ("ForAllAntecedent " ++ show a) `thenShow` s
showProof (OrElimLeftSuccedent s)    = "OrElimLeftSuccedent"           `thenShow` s
showProof (OrElimRightSuccedent s)   = "OrElimRightSuccedent"          `thenShow` s
showProof (NegationSuccedent s)      = "NegationSuccedent"             `thenShow` s
showProof (NegationAntecedent s)     = "NegationAntecedent"            `thenShow` s
showProof (AndElimLeftAntecedent s)  = "AndElimLeftAntecedent"         `thenShow` s
showProof (AndElimRightAntecedent s) = "AndElimRightAntecedent"        `thenShow` s
showProof (PermuteSuccedent s)       = "PermuteSuccedent"              `thenShow` s
showProof (PermuteAntecedent s)      = "PermuteAntecedent"             `thenShow` s
showProof (ForAllSuccedent f) = do
    x      <- fresh
    shownF <- showProof (f x)
    return $ "ForAllSuccedent (" ++ show x ++ " -> " ++ shownF ++ ")"
showProof (OrElimAntecedent l r) = do
    showL <- showProof l
    showR <- showProof r
    return ("OrElimAntecedent (" ++ showL ++ ") (" ++ showR ++ ")")
showProof (AndElimSuccedent l r) =  do
    showL <- showProof l
    showR <- showProof r
    return ("AndElimSuccedent (" ++ showL ++ ") (" ++ showR ++ ")")
