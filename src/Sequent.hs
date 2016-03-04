module Sequent where

import           Control.Arrow     ((&&&))

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
excludedMiddle a = [] |- [TTerm (Var a) `Or` Not (TTerm (Var a))]

proofExcludedMiddle :: Proof
proofExcludedMiddle
      = ContractionSuccedent
      $ OrElimLeftSuccedent
      $ PermuteSuccedent
      $ OrElimRightSuccedent
      $ NegationSuccedent Axiom

checkExcludedMiddle :: (Maybe (), String)
checkExcludedMiddle = runProof (excludedMiddle &&& const proofExcludedMiddle)


trivialOr :: (Variable, Variable) -> Judgment
trivialOr (a, b) = [TTerm (Var a) `Or` TTerm (Var b)]
                |- [TTerm (Var a) `Or` TTerm (Var b)]

proofTrivialOr :: Proof
proofTrivialOr = OrElimAntecedent
                    (OrElimLeftSuccedent Axiom)
                    (OrElimRightSuccedent Axiom)

checkTrivialOr :: (Maybe (), String)
checkTrivialOr = runProof (trivialOr &&& const proofTrivialOr)


orCommutative :: (Variable, Variable) -> Judgment
orCommutative (a, b) = [TTerm (Var a) `Or` TTerm (Var b)]
                    |- [TTerm (Var b) `Or` TTerm (Var a)]

proofOrCommutative :: Proof
proofOrCommutative = OrElimAntecedent
                            (OrElimRightSuccedent Axiom)
                            (OrElimLeftSuccedent Axiom)

checkOrCommutative :: (Maybe (), String)
checkOrCommutative = runProof (orCommutative &&& const proofOrCommutative)


deMorganOr :: (Variable, Variable) -> Judgment
deMorganOr (a, b) = [Not (TTerm (Var a) `And` TTerm (Var b))]
                 |- [Not (TTerm $ Var a) `Or` Not (TTerm $ Var b)]

proofDeMorganOr :: Proof
proofDeMorganOr = NegationAntecedent
                $ AndElimSuccedent
                    ( PermuteSuccedent
                    $ OrElimLeftSuccedent
                    $ NegationSuccedent Axiom )
                    ( PermuteSuccedent
                    $ OrElimRightSuccedent
                    $ NegationSuccedent Axiom )

checkDeMorganOr :: (Maybe (), String)
checkDeMorganOr = runProof (deMorganOr &&& const proofDeMorganOr)


deMorganAnd :: (Variable, Variable) -> Judgment
deMorganAnd (a, b) = [Not (TTerm (Var a) `Or` TTerm (Var b))]
                  |- [Not (TTerm $ Var a) `And` Not (TTerm $ Var b)]

proofDeMorganAnd :: Proof
proofDeMorganAnd = NegationAntecedent
                 $ PermuteSuccedent
                 $ AndElimSuccedent
                    ( NegationSuccedent
                    $ OrElimLeftSuccedent Axiom )
                    ( NegationSuccedent
                    $ OrElimRightSuccedent Axiom )

checkDeMorganAnd :: (Maybe (), String)
checkDeMorganAnd = runProof (deMorganAnd &&& const proofDeMorganAnd)

nestedForAll :: Predicate2 -> Judgment
nestedForAll p = [ForAll $ \a -> ForAll $ \b -> TTerm $ App2 p (a, b)]
              |- [ForAll $ \b -> ForAll $ \a -> TTerm $ App2 p (a, b)]

proofNestedForAll :: Predicate2 -> Proof
proofNestedForAll _ = ForAllSuccedent $ \b ->
                      ForAllSuccedent $ \a ->
                          ForAllAntecedent (Var a)
                        $ ForAllAntecedent (Var b) Axiom

checkNestedForAll :: (Maybe (), String)
checkNestedForAll = runProof (nestedForAll &&& proofNestedForAll)



theoremWithPredicateIntro :: (Predicate1, Predicate1) -> Judgment
theoremWithPredicateIntro (p, f) = [ForAll $ \x -> TTerm $ App1 p (App1 f x)]
                                |- [ForAll $ \x -> TTerm $ App1 p (App1 f (App1 f x))]

proofTheoremWithPredicateIntro :: (Predicate1, Predicate1) -> Proof
proofTheoremWithPredicateIntro (_, f) = ForAllSuccedent $ \x ->
                                        ForAllAntecedent (App1 f (Var x)) Axiom

checkTheoremWithPredicateIntro :: (Maybe (), String)
checkTheoremWithPredicateIntro = runProof ( theoremWithPredicateIntro
                                        &&& proofTheoremWithPredicateIntro)


theoremDoublePredicate :: (Predicate1, Predicate1) -> Judgment
theoremDoublePredicate (p, f) = [ForAll $ \x -> TTerm (App1 p x) :-> TTerm (App1 p (App1 f x))]
                             |- [ForAll $ \x -> TTerm (App1 p x) :-> TTerm (App1 p (App1 f (App1 f x)))]

proofTheoremDoublePredicate :: (Predicate1, Predicate1) -> Proof
proofTheoremDoublePredicate (_, f) = ContractionAntecedent
                                   $ ForAllSuccedent $ \x ->
                                        ImplicationSuccedent
                                      $ PermuteAntecedent
                                      $ ForAllAntecedent (Var x)
                                      $ ImplicationAntecedent
                                              Axiom
                                              ( PermuteAntecedent
                                              $ WeakenAntecedent
                                              $ PermuteAntecedent
                                              $ ForAllAntecedent (App1 f (Var x))
                                              $ ImplicationAntecedent
                                                    Axiom
                                                    Axiom
                                              )

checkTheoremDoublePredicate :: (Maybe (), String)
checkTheoremDoublePredicate = runProof ( theoremDoublePredicate
                                     &&& proofTheoremDoublePredicate)
