module Sequent.ProofTerm
    ( Step(..)
    , Proof
    , contractionSuccedent, forAllSuccedent, forAllAntecedent
    , orElimLeftSuccedent , orElimRightSuccedent, negationSuccedent
    , negationAntecedent, orElimAntecedent, andElimSuccedent
    , andElimLeftAntecedent, andElimRightAntecedent, permuteSuccedent
    , permuteAntecedent
    ) where

import           Sequent.Env (Variable)

data Step
  = ContractionSuccedent
  | ForAllSuccedent
  | ForAllAntecedent Variable
  | OrElimLeftSuccedent
  | OrElimRightSuccedent
  | NegationSuccedent
  | NegationAntecedent
  | OrElimAntecedent Proof Proof
  | AndElimSuccedent Proof Proof
  | AndElimLeftAntecedent
  | AndElimRightAntecedent
  | PermuteSuccedent
  | PermuteAntecedent
  deriving (Show, Eq)

type Proof = [Step]

-- helpers

contractionSuccedent :: Proof
contractionSuccedent = [ContractionSuccedent]

forAllSuccedent :: Proof
forAllSuccedent = [ForAllSuccedent]

forAllAntecedent :: Variable -> Proof
forAllAntecedent a = [ForAllAntecedent a]

orElimLeftSuccedent :: Proof
orElimLeftSuccedent = [OrElimLeftSuccedent]

orElimRightSuccedent :: Proof
orElimRightSuccedent = [OrElimRightSuccedent]

negationSuccedent :: Proof
negationSuccedent = [NegationSuccedent]

negationAntecedent :: Proof
negationAntecedent = [NegationAntecedent]

orElimAntecedent :: Proof -> Proof -> Proof
orElimAntecedent l r = [OrElimAntecedent l r]

andElimSuccedent :: Proof -> Proof -> Proof
andElimSuccedent l r = [AndElimSuccedent l r]

andElimLeftAntecedent :: Proof
andElimLeftAntecedent = [AndElimLeftAntecedent]

andElimRightAntecedent :: Proof
andElimRightAntecedent = [AndElimRightAntecedent]

permuteSuccedent :: Proof
permuteSuccedent = [PermuteSuccedent]

permuteAntecedent :: Proof
permuteAntecedent = [PermuteAntecedent]
