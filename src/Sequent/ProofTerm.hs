module Sequent.ProofTerm
    ( Step(..)
    , Proof
    , contractionSuccedent, forAllSuccedent, orElimLeftSuccedent
    , orElimRightSuccedent, negationSuccedent, orElimAntecedent
    , permuteSuccedent, permuteAntecedent
    ) where

data Step
  = ContractionSuccedent
  | ForAllSuccedent
  | OrElimLeftSuccedent
  | OrElimRightSuccedent
  | NegationSuccedent
  | OrElimAntecedent Proof Proof
  | PermuteSuccedent
  | PermuteAntecedent
  deriving (Show, Eq)

type Proof = [Step]

-- helpers

contractionSuccedent :: Proof
contractionSuccedent = [ContractionSuccedent]

forAllSuccedent :: Proof
forAllSuccedent = [ForAllSuccedent]

orElimLeftSuccedent :: Proof
orElimLeftSuccedent = [OrElimLeftSuccedent]

orElimRightSuccedent :: Proof
orElimRightSuccedent = [OrElimRightSuccedent]

negationSuccedent :: Proof
negationSuccedent = [NegationSuccedent]

orElimAntecedent :: Proof -> Proof -> Proof
orElimAntecedent l r = [OrElimAntecedent l r]

permuteSuccedent :: Proof
permuteSuccedent = [PermuteSuccedent]

permuteAntecedent :: Proof
permuteAntecedent = [PermuteAntecedent]
