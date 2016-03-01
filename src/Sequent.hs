module Sequent where

import           Data.Monoid       ((<>))

import           Sequent.Check
import           Sequent.Env
import           Sequent.Inference
import           Sequent.Introduce
import           Sequent.ProofTerm
import           Sequent.Theorem

-- TODO Move me :()
runProof :: Introduce a => (a -> Theorem) -> Proof -> (Maybe (), String)
runProof theorem proof = evalCheck (check proof (runIntros theorem))

excludedMiddle :: Variable -> Theorem
excludedMiddle a = [] |- [Var a `Or` Not (Var a)]

proofExcludedMiddle :: Proof
proofExcludedMiddle
      = contractionRight
     <> leftOrElimRight
     <> permuteRight
     <> rightOrElimRight
     <> negationRight

checkExcludedMiddle = runProof excludedMiddle proofExcludedMiddle


trivialOr :: (Variable, Variable) -> Theorem
trivialOr (a, b) = [Var a `Or` Var b] |- [Var a `Or` Var b]

proofTrivialOr :: Proof
proofTrivialOr = orElimLeft leftOrElimRight rightOrElimRight

checkTrivialOr = runProof trivialOr proofTrivialOr
