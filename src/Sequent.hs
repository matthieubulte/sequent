module Sequent where

import           Data.Monoid       ((<>))

import           Sequent.Check
import           Sequent.Env
import           Sequent.Inference
import           Sequent.Introduce
import           Sequent.ProofTerm
import           Sequent.Theorem

-- TODO Move me :()
runProof :: Introduce a => (a -> Judgment) -> Proof -> (Maybe (), String)
runProof judgment proof = evalCheck (check proof (runIntros judgment))

excludedMiddle :: Variable -> Judgment
excludedMiddle a = [] |- [Var a `Or` Not (Var a)]

proofExcludedMiddle :: Proof
proofExcludedMiddle
      = contractionSuccedent
     <> orElimLeftSuccedent
     <> permuteSuccedent
     <> orElimRightSuccedent
     <> negationSuccedent

checkExcludedMiddle = runProof excludedMiddle proofExcludedMiddle


trivialOr :: (Variable, Variable) -> Judgment
trivialOr (a, b) = [Var a `Or` Var b] |- [Var a `Or` Var b]

proofTrivialOr :: Proof
proofTrivialOr = orElimAntecedent orElimLeftSuccedent orElimRightSuccedent

checkTrivialOr = runProof trivialOr proofTrivialOr


orCommutative :: (Variable, Variable) -> Judgment
orCommutative (a, b) = [Var a `Or` Var b] |- [Var b `Or` Var a]

proofOrCommutative :: Proof
proofOrCommutative = orElimAntecedent orElimRightSuccedent orElimLeftSuccedent

checkOrCommutative = runProof orCommutative proofOrCommutative
