module Sequent where

import           Data.Monoid       ((<>))

import           Sequent.Check
import           Sequent.Env
import           Sequent.Inference
import           Sequent.Introduce
import           Sequent.ProofTerm
import           Sequent.Theorem

import           Control.Arrow     ((&&&))

-- TODO Move me :()
runProof :: Introduce a => (a -> (Judgment, Proof)) -> (Maybe (), String)
runProof judgmentProof = let (judgment, proof) = runIntros judgmentProof
                         in evalCheck (check proof judgment)

excludedMiddle :: Variable -> Judgment
excludedMiddle a = [] |- [Var a `Or` Not (Var a)]

proofExcludedMiddle :: Proof
proofExcludedMiddle
      = contractionSuccedent
     <> orElimLeftSuccedent
     <> permuteSuccedent
     <> orElimRightSuccedent
     <> negationSuccedent

checkExcludedMiddle = runProof (excludedMiddle &&& const proofExcludedMiddle)


trivialOr :: (Variable, Variable) -> Judgment
trivialOr (a, b) = [Var a `Or` Var b] |- [Var a `Or` Var b]

proofTrivialOr :: Proof
proofTrivialOr = orElimAntecedent orElimLeftSuccedent orElimRightSuccedent

checkTrivialOr = runProof (trivialOr &&& const proofTrivialOr)


orCommutative :: (Variable, Variable) -> Judgment
orCommutative (a, b) = [Var a `Or` Var b] |- [Var b `Or` Var a]

proofOrCommutative :: Proof
proofOrCommutative = orElimAntecedent orElimRightSuccedent orElimLeftSuccedent

checkOrCommutative = runProof (orCommutative &&& const proofOrCommutative)


deMorganOr :: (Variable, Variable) -> Judgment
deMorganOr (a, b) = [Not (Var a `And` Var b)] |- [Not (Var a) `Or` Not (Var b)]

proofDeMorganOr :: Proof
proofDeMorganOr = negationAntecedent
               <> andElimSuccedent
                    (permuteSuccedent <> orElimLeftSuccedent <> negationSuccedent)
                    (permuteSuccedent <> orElimRightSuccedent <> negationSuccedent)

checkDeMorganOr = runProof (deMorganOr &&& const proofDeMorganOr)


deMorganAnd :: (Variable, Variable) -> Judgment
deMorganAnd (a, b) = [Not (Var a `Or` Var b)] |- [Not (Var a) `And` Not (Var b)]

proofDeMorganAnd :: Proof
proofDeMorganAnd = negationAntecedent
                <> permuteSuccedent
                <> andElimSuccedent
                    (negationSuccedent <> orElimLeftSuccedent)
                    (negationSuccedent <> orElimRightSuccedent)

checkDeMorganAnd = runProof (deMorganAnd &&& const proofDeMorganAnd)
