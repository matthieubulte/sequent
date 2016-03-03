module Sequent where

import           Control.Arrow       ((&&&))
import           Control.Monad.Trans (lift)
import           Data.Monoid         ((<>))

import           Sequent.Check
import           Sequent.Env
import           Sequent.Inference
import           Sequent.Introduce
import           Sequent.Proof
import           Sequent.Theorem

-- TODO Move me :()
runProof :: Introduce a => (a -> (Judgment, Proof)) -> (Maybe (), String)
runProof judgmentProof = evalCheck $ do
    (judgment, proof) <- liftEnv (runIntros judgmentProof)
    check proof judgment

excludedMiddle :: Variable -> Judgment
excludedMiddle a = [] |- [Var a `Or` Not (Var a)]

proofExcludedMiddle :: Proof
proofExcludedMiddle
      = ContractionSuccedent
      $ OrElimLeftSuccedent
      $ PermuteSuccedent
      $ OrElimRightSuccedent
      $ NegationSuccedent Axiom

checkExcludedMiddle = runProof (excludedMiddle &&& const proofExcludedMiddle)


trivialOr :: (Variable, Variable) -> Judgment
trivialOr (a, b) = [Var a `Or` Var b] |- [Var a `Or` Var b]

proofTrivialOr :: Proof
proofTrivialOr = OrElimAntecedent
                    (OrElimLeftSuccedent Axiom)
                    (OrElimRightSuccedent Axiom)

checkTrivialOr = runProof (trivialOr &&& const proofTrivialOr)


orCommutative :: (Variable, Variable) -> Judgment
orCommutative (a, b) = [Var a `Or` Var b] |- [Var b `Or` Var a]

proofOrCommutative :: Proof
proofOrCommutative = OrElimAntecedent
                            (OrElimRightSuccedent Axiom)
                            (OrElimLeftSuccedent Axiom)

checkOrCommutative = runProof (orCommutative &&& const proofOrCommutative)


deMorganOr :: (Variable, Variable) -> Judgment
deMorganOr (a, b) = [Not (Var a `And` Var b)] |- [Not (Var a) `Or` Not (Var b)]

proofDeMorganOr :: Proof
proofDeMorganOr = NegationAntecedent
                $ AndElimSuccedent
                    ( PermuteSuccedent
                    $ OrElimLeftSuccedent
                    $ NegationSuccedent Axiom )
                    ( PermuteSuccedent
                    $ OrElimRightSuccedent
                    $ NegationSuccedent Axiom )

checkDeMorganOr = runProof (deMorganOr &&& const proofDeMorganOr)


deMorganAnd :: (Variable, Variable) -> Judgment
deMorganAnd (a, b) = [Not (Var a `Or` Var b)] |- [Not (Var a) `And` Not (Var b)]

proofDeMorganAnd :: Proof
proofDeMorganAnd = NegationAntecedent
                 $ PermuteSuccedent
                 $ AndElimSuccedent
                    ( NegationSuccedent
                    $ OrElimLeftSuccedent Axiom )
                    ( NegationSuccedent
                    $ OrElimRightSuccedent Axiom )

checkDeMorganAnd = runProof (deMorganAnd &&& const proofDeMorganAnd)

nestedForAll :: Variable -> Judgment
nestedForAll p = [ForAll $ \a -> ForAll $ \b -> Pred2 p (a, b)]
              |- [ForAll $ \b -> ForAll $ \a -> Pred2 p (a, b)]

proofNestedForAll :: Variable -> Proof
proofNestedForAll p = ForAllSuccedent $ \b ->
                      ForAllSuccedent $ \a ->
                          ForAllAntecedent a
                        $ ForAllAntecedent b Axiom

checkNestedForAll = runProof (nestedForAll &&& proofNestedForAll)
