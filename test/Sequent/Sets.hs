
module Sequent.Sets where

import           Sequent

ap :: Predicate2 -> Term -> Term -> Theorem
ap p x y = TTerm $ App2 p x y

equiv :: Theorem -> Theorem -> Theorem
equiv t t' = And (t :-> t') (t' :-> t)

defSubset :: (Predicate2, Predicate2) -> Theorem
defSubset (subs, cont) =
    let contains = ap cont
        subset = ap subs
    in
        ForAll $ \s -> ForAll $ \s' ->
            (s `subset` s') `equiv` (ForAll $ \x -> (s `contains` x) :-> (s' `contains` x))

defEqual :: (Predicate2, Predicate2) -> Theorem
defEqual (equ, subs) =
    let subset = ap subs
        equals = ap equ
    in
        ForAll $ \s -> ForAll $ \s' ->
            (s `equals` s') `equiv` ((s `subset` s') `And` (s' `subset` s))

subsetSymmetric :: (Predicate2, Predicate2, Term) -> Judgment
subsetSymmetric (cont, subs, set) = [ defSubset (subs, cont) ]
                                 |- [ ap subs set set ]

proofSubsetSymmetric :: (Predicate2, Predicate2, Term) -> Proof
proofSubsetSymmetric (_, _, set) =
      ForAllAntecedent set
    $ ForAllAntecedent set
    $ AndElimRightAntecedent
    $ ImplicationAntecedent
        (ForAllSuccedent $ \_ -> ImplicationSuccedent Axiom)
        Axiom

equalSymmetric :: (Predicate2, Predicate2, Predicate2, Term) -> Judgment
equalSymmetric (cont, subs, equ, set) = [ defSubset (subs, cont) , defEqual (equ, subs) ]
                                     |- [ ap equ set set ]

proofEqualSymmetric :: (Predicate2, Predicate2, Predicate2, Term) -> Proof
proofEqualSymmetric (cont, subs, _, set) =
        PermuteAntecedent
      $ ForAllAntecedent set
      $ ForAllAntecedent set
      $ AndElimRightAntecedent
      $ ImplicationAntecedent
        (AndElimSuccedent
            (proofSubsetSymmetric (cont, subs, set))
            (proofSubsetSymmetric (cont, subs, set))
        )
        Axiom


boolSetContains :: (Predicate2, Term, Term, Term) -> Theorem
boolSetContains (cont, set, true, false) =
    let contains = ap cont
    in
        ForAll $ \x -> (set `contains` x) `equiv` (TTerm x `equiv` (TTerm true `Or` TTerm false))

orOp :: (Predicate2, Term, Term) -> [Theorem]
orOp (orS, true, false) =
    let or' = ap orS
    in
        [ or' true  true  `equiv` TTerm true
        , or' true  false `equiv` TTerm true
        , or' false true  `equiv` TTerm true
        , or' false false `equiv` TTerm false
        ]

orClosed :: (Predicate2, Predicate2, Term, Term, Term) -> Judgment
orClosed (contains, or', bools, true, false) =
    (boolSetContains (contains, bools, true, false) : orOp (or', true, false))
    |-
    [ForAll $ \x -> ForAll $ \y -> (inBools x `And` inBools y) :-> inBools (App2 or' x y)]

    where
        inBools :: Term -> Theorem
        inBools = ap contains bools

proofOrClosed :: (Predicate2, Predicate2, Term, Term, Term) -> Proof
proofOrClosed (contains, or', bools, true, false) =
    ForAllSuccedent $ \x ->
    ForAllSuccedent $ \y ->
          ImplicationSuccedent
          Axiom
