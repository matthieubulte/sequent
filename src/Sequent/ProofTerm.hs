module Sequent.ProofTerm
    ( Step(..)
    , Proof
    , forAllRight, contractionRight, leftOrElimRight, rightOrElimRight
    , permuteRight, permuteLeft, negationRight, orElimLeft
    ) where

data Step
  = ForAllRight
  | ContractionRight
  | LeftOrElimRight
  | RightOrElimRight
  | NegationRight
  | PermuteRight
  | PermuteLeft
  | OrElimLeft Proof Proof
  deriving (Show, Eq)

type Proof = [Step]

-- helpers

forAllRight :: Proof
forAllRight = [ForAllRight]

contractionRight :: Proof
contractionRight = [ContractionRight]

leftOrElimRight :: Proof
leftOrElimRight = [LeftOrElimRight]

rightOrElimRight :: Proof
rightOrElimRight = [RightOrElimRight]

permuteRight :: Proof
permuteRight = [PermuteRight]

permuteLeft :: Proof
permuteLeft = [PermuteLeft]

negationRight :: Proof
negationRight = [NegationRight]

orElimLeft :: Proof -> Proof -> Proof
orElimLeft l r = [OrElimLeft l r]
