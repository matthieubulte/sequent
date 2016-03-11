{-# LANGUAGE FlexibleInstances #-}

module Sequent.Peano where

import           Sequent
import           Sequent.Sugar

evalProof :: Introduce a => (a -> (Judgment, Proof)) -> (Maybe (), String)
evalProof judgmentProof = evalCheck $ do
    (judgment, proof) <- liftEnv (runIntros judgmentProof)
    check proof judgment

-- Peano axioms

type IsNat = Predicate1
type NatEq = Predicate2
type Zero  = Variable
type Suc   = Predicate1

type NatDef = ( IsNat
              , NatEq
              , Zero
              , Suc
              )

-- inductive definition of the nat set
zeroIsNat :: NatDef -> Theorem
zeroIsNat (isnat, _, zero, _) = toTheorem (isnat <.> zero)

succNatIsNat :: NatDef -> Theorem
succNatIsNat (isnat, _, _, suc) =
    forallOf isnat $ \n -> isnat <.> (suc <.> n)

-- equality has a base rule and the standard properties
zeroIsNoSuccessor :: NatDef -> Theorem
zeroIsNoSuccessor (isnat, nateq, zero, suc) =
    not' $ forsomeOf isnat (\n -> nateq <..> (zero, suc <.> n))

sucIsInjective :: NatDef -> Theorem
sucIsInjective (isnat, nateq, _, suc) =
    forallOf isnat $ \x ->
    forallOf isnat $ \y ->
                nateq <..> (suc <.> x, suc <.> y)
                              ==>
                        nateq <..> (x, y)

eqIsReflexive :: NatDef -> Theorem
eqIsReflexive (isnat, nateq, _, _) = forallOf isnat $ \x -> nateq <..> (x, x)

eqIsSymmetric :: NatDef -> Theorem
eqIsSymmetric (isnat, nateq, _, _) =
    forallOf isnat $ \x ->
    forallOf isnat $ \y ->
                   nateq <..> (x, y)
                          ==>
                   nateq <..> (y, x)

eqIsTransitive :: NatDef -> Theorem
eqIsTransitive (isnat, nateq, _, _) =
    forallOf isnat $ \x ->
    forallOf isnat $ \y ->
    forallOf isnat $ \z ->
                nateq <..> (x, y) &&& nateq <..> (y, z)
                                ==>
                        nateq <..> (x, z)

eqIsClosed :: NatDef -> Theorem
eqIsClosed (isnat, nateq, _, _) =
    forall $ \x ->
    forallOf isnat $ \y ->
            nateq <..> (x, y)
                   ==>
               isnat <.> y

-- probably the most important axiom
natInduction :: NatDef -> Predicate1 -> Theorem
natInduction (isnat, _, zero, suc) p =
        p <.> zero &&& forallOf isnat (\n -> p <.> n ==> p <.> (suc <.> n))
                                        ==>
                            forallOf isnat (\n -> p <.> n)



natAxioms :: NatDef -> [Theorem]
natAxioms nat = ($ nat) <$> [ zeroIsNat
                            , succNatIsNat
                            , zeroIsNoSuccessor
                            , sucIsInjective
                            , eqIsReflexive
                            , eqIsSymmetric
                            , eqIsTransitive
                            , eqIsClosed
                            ]

--

defPred :: NatDef -> Predicate2 -> [Theorem]
defPred (isnat, nateq, _, suc) ispred = return $
        forallOf isnat $ \x ->
        forallOf isnat $ \y ->
                    ispred <..> (x, y) <==> nateq <..> (suc <.> x, y)

zeroHasNoPred :: NatDef -> Predicate2 -> [Theorem]
zeroHasNoPred (isnat, _, zero, _) ispred = return $
        forallOf isnat (\n -> not' $ ispred <..> (n, zero))

judgZeroHasNoPred :: (IsNat, NatEq, Zero, Suc, Predicate2) -> Judgment
judgZeroHasNoPred (isnat, nateq, zero, suc, ispred) =
    let nat = (isnat, nateq, zero, suc)
    in (defPred nat ispred ++ natAxioms nat) |- zeroHasNoPred nat ispred

proofZeroHasNoPred :: NatDef -> Proof
proofZeroHasNoPred _ =
    ForAllSuccedent $ \n ->
          ForAllAntecedent n
        $ ImplicationSuccedent
        $ NegationSuccedent
        $ RotateLeftAntecedent
        $ RotateLeftAntecedent
        $ RotateLeftAntecedent
        $ RotateLeftAntecedent
        $ RotateLeftAntecedent
        $ NegationAntecedent
        $ ForSomeSuccedent Axiom


foo :: (IsNat, NatEq, Zero, Suc, Predicate2) -> (Judgment, Proof)
foo ps@(isnat, nateq, zero, suc, _) =
    let nat = (isnat, nateq, zero, suc)
    in (judgZeroHasNoPred ps, proofZeroHasNoPred nat)
