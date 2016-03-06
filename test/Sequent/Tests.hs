module Sequent.Tests where

import           Data.Maybe (isJust)
import           Sequent

runProof :: Introduce a => (a -> (Judgment, Proof)) -> Bool
runProof judgmentProof = isJust . fst . evalCheck $ do
    (judgment, proof) <- liftEnv (runIntros judgmentProof)
    check proof judgment


excludedMiddle :: Variable -> Judgment
excludedMiddle a = [] |- [TTerm (Var a) `Or` Not (TTerm (Var a))]

proofExcludedMiddle :: a -> Proof
proofExcludedMiddle _
      = ContractionSuccedent
      $ OrElimLeftSuccedent
      $ PermuteSuccedent
      $ OrElimRightSuccedent
      $ NegationSuccedent Axiom

--

trivialOr :: (Variable, Variable) -> Judgment
trivialOr (a, b) = [TTerm (Var a) `Or` TTerm (Var b)]
                |- [TTerm (Var a) `Or` TTerm (Var b)]

proofTrivialOr :: a -> Proof
proofTrivialOr _ = OrElimAntecedent
                    (OrElimLeftSuccedent Axiom)
                    (OrElimRightSuccedent Axiom)

--

orCommutative :: (Variable, Variable) -> Judgment
orCommutative (a, b) = [TTerm (Var a) `Or` TTerm (Var b)]
                    |- [TTerm (Var b) `Or` TTerm (Var a)]

proofOrCommutative :: a -> Proof
proofOrCommutative _ = OrElimAntecedent
                            (OrElimRightSuccedent Axiom)
                            (OrElimLeftSuccedent Axiom)

--

deMorganOr :: (Variable, Variable) -> Judgment
deMorganOr (a, b) = [Not (TTerm (Var a) `And` TTerm (Var b))]
                 |- [Not (TTerm $ Var a) `Or` Not (TTerm $ Var b)]

proofDeMorganOr :: a -> Proof
proofDeMorganOr _ = NegationAntecedent
                  $ AndElimSuccedent
                      ( PermuteSuccedent
                      $ OrElimLeftSuccedent
                      $ NegationSuccedent Axiom )
                      ( PermuteSuccedent
                      $ OrElimRightSuccedent
                      $ NegationSuccedent Axiom )

--

deMorganAnd :: (Variable, Variable) -> Judgment
deMorganAnd (a, b) = [Not (TTerm (Var a) `Or` TTerm (Var b))]
                  |- [Not (TTerm $ Var a) `And` Not (TTerm $ Var b)]

proofDeMorganAnd :: a -> Proof
proofDeMorganAnd _ = NegationAntecedent
                   $ PermuteSuccedent
                   $ AndElimSuccedent
                      ( NegationSuccedent
                      $ OrElimLeftSuccedent Axiom )
                      ( NegationSuccedent
                      $ OrElimRightSuccedent Axiom )

--

nestedForAll :: Predicate2 -> Judgment
nestedForAll p = [ForAll $ \a -> ForAll $ \b -> TTerm $ App2 p (a, b)]
              |- [ForAll $ \b -> ForAll $ \a -> TTerm $ App2 p (a, b)]

proofNestedForAll :: Predicate2 -> Proof
proofNestedForAll _ = ForAllSuccedent $ \b ->
                      ForAllSuccedent $ \a ->
                          ForAllAntecedent a
                        $ ForAllAntecedent b Axiom

--

judgmentWithPredicateIntro :: (Predicate1, Predicate1) -> Judgment
judgmentWithPredicateIntro (p, f) = [ForAll $ \x -> TTerm $ App1 p (App1 f x)]
                                 |- [ForAll $ \x -> TTerm $ App1 p (App1 f (App1 f x))]

proofJudgmentWithPredicateIntro :: (Predicate1, Predicate1) -> Proof
proofJudgmentWithPredicateIntro (_, f) = ForAllSuccedent $ \x ->
                                         ForAllAntecedent (App1 f x) Axiom

--

doublePredicate :: (Predicate1, Predicate1) -> Judgment
doublePredicate (p, f) = [ForAll $ \x -> TTerm (App1 p x) :-> TTerm (App1 p (App1 f x))]
                      |- [ForAll $ \x -> TTerm (App1 p x) :-> TTerm (App1 p (App1 f (App1 f x)))]

proofDoublePredicate :: (Predicate1, Predicate1) -> Proof
proofDoublePredicate (_, f) = ContractionAntecedent
                            $ ForAllSuccedent $ \x ->
                                 ImplicationSuccedent
                               $ PermuteAntecedent
                               $ ForAllAntecedent x
                               $ ImplicationAntecedent
                                       Axiom
                                       ( PermuteAntecedent
                                       $ WeakenAntecedent
                                       $ PermuteAntecedent
                                       $ ForAllAntecedent (App1 f x)
                                       $ ImplicationAntecedent
                                            Axiom
                                            Axiom
                                       )

--

existsForAll :: Predicate2 -> Judgment
existsForAll p = [ThereExists $ \x -> ForAll $ \y -> TTerm (App2 p (x, y))]
              |- [ForAll $ \y -> ThereExists $ \x -> TTerm (App2 p (x, y))]

proofExistsForAll :: Predicate2 -> Proof
proofExistsForAll _ = ForAllSuccedent $ \y ->
                      ThereExistsAntecedent $ \x ->
                      ThereExistsSuccedent x $
                      ForAllAntecedent y
                      Axiom
