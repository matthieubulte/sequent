module Sequent.Proof
    ( Proof(..)
    ) where

import           Control.Arrow     ((&&&))

import           Sequent.Env       (Env, evalEnv)
import           Sequent.Introduce (introduce)
import           Sequent.Term      (Term)

data Proof
  = ContractionSuccedent Proof
  | ContractionAntecedent Proof
  | WeakenAntecedent Proof
  | WeakenSuccedent Proof
  | ForAllSuccedent (Term -> Proof)
  | ForAllAntecedent Term Proof
  | ThereExistsSuccedent Term Proof
  | ThereExistsAntecedent (Term -> Proof)
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
  | ImplicationSuccedent Proof
  | ImplicationAntecedent Proof Proof
  | Axiom

instance Eq Proof where
    a == b = evalEnv (eqProofs a b)

instance Show Proof where
    show = showProof

-- to show or test equality of two theorems we must be able to replace
-- quantifiers with contrete variables in order to eliminate functions
-- in our haskell representation of the theorem and explore the subtheorem

eqBranch :: Proof -> Proof -> Proof -> Proof -> Env Bool
eqBranch l r l' r' = (&&) <$> eqProofs l l' <*> eqProofs r r'

eqProofs :: Proof -> Proof -> Env Bool
eqProofs Axiom Axiom = return True
eqProofs (ContractionSuccedent s)   (ContractionSuccedent s')   = eqProofs s s'
eqProofs (ContractionAntecedent s)  (ContractionAntecedent s')  = eqProofs s s'
eqProofs (WeakenSuccedent s)        (WeakenSuccedent s')        = eqProofs s s'
eqProofs (WeakenAntecedent s)       (WeakenAntecedent s')       = eqProofs s s'
eqProofs (OrElimLeftSuccedent s)    (OrElimLeftSuccedent s')    = eqProofs s s'
eqProofs (OrElimRightSuccedent s)   (OrElimRightSuccedent s')   = eqProofs s s'
eqProofs (NegationSuccedent s)      (NegationSuccedent s')      = eqProofs s s'
eqProofs (NegationAntecedent s)     (NegationAntecedent s')     = eqProofs s s'
eqProofs (AndElimLeftAntecedent s)  (AndElimLeftAntecedent s')  = eqProofs s s'
eqProofs (AndElimRightAntecedent s) (AndElimRightAntecedent s') = eqProofs s s'
eqProofs (PermuteSuccedent s)       (PermuteSuccedent s')       = eqProofs s s'
eqProofs (PermuteAntecedent s)      (PermuteAntecedent s')      = eqProofs s s'
eqProofs (ImplicationSuccedent s)   (ImplicationSuccedent s')   = eqProofs s s'
eqProofs (ForAllAntecedent a s)     (ForAllAntecedent a' s')    =
    (a == a' &&) <$> eqProofs s s'
eqProofs (ThereExistsSuccedent a s) (ThereExistsSuccedent a' s') =
    (a == a' &&) <$> eqProofs s s'
eqProofs (ForAllSuccedent f) (ForAllSuccedent f') =
    introduce >>= uncurry eqProofs . (f &&& f')
eqProofs (ThereExistsAntecedent f) (ThereExistsAntecedent f') =
    introduce >>= uncurry eqProofs . (f &&& f')
eqProofs (OrElimAntecedent l r)      (OrElimAntecedent l' r')      = eqBranch l r l' r'
eqProofs (AndElimSuccedent l r)      (AndElimSuccedent l' r')      = eqBranch l r l' r'
eqProofs (ImplicationAntecedent l r) (ImplicationAntecedent l' r') = eqBranch l r l' r'
eqProofs _ _ = return False

showProof :: Proof -> String
showProof Axiom                       = "Axiom"
showProof (ContractionSuccedent _)    = "ContractionSuccedent"
showProof (ContractionAntecedent _)   = "ContractionAntecedent"
showProof (WeakenSuccedent _)         = "WeakenSuccedent"
showProof (WeakenAntecedent _)        = "WeakenAntecedent"
showProof (ForAllAntecedent a _)      = "ForAllAntecedent " ++ show a
showProof (ForAllSuccedent _)         = "ForAllSuccedent"
showProof (ThereExistsSuccedent a _) = "ThereExistsSuccedent " ++ show a
showProof (ThereExistsAntecedent _)  = "ThereExistsAntecedent"
showProof (OrElimLeftSuccedent _)     = "OrElimLeftSuccedent"
showProof (OrElimRightSuccedent _)    = "OrElimRightSuccedent"
showProof (NegationSuccedent _)       = "NegationSuccedent"
showProof (NegationAntecedent _)      = "NegationAntecedent"
showProof (AndElimLeftAntecedent _)   = "AndElimLeftAntecedent"
showProof (AndElimRightAntecedent _)  = "AndElimRightAntecedent"
showProof (PermuteSuccedent _)        = "PermuteSuccedent"
showProof (PermuteAntecedent _)       = "PermuteAntecedent"
showProof (ImplicationSuccedent _)    = "ImplicationSuccedent"
showProof (OrElimAntecedent _ _)      = "OrElimAntecedent"
showProof (AndElimSuccedent _ _)      = "AndElimSuccedent"
showProof (ImplicationAntecedent _ _) = "ImplicationAntecedent"
