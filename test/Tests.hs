
import           Control.Arrow ((&&&))
import           Sequent       (Introduce, Judgment, Proof)
import           Sequent.Peano
import           Sequent.Tests
import           Test.HUnit    (Counts, Test (..), assertBool, runTestTT)

check' :: Introduce a => String -> (a -> (Judgment, Proof)) -> Test
check' s f =  TestCase $ assertBool s (runProof f)

check :: Introduce a => String -> (a -> Judgment) -> (a -> Proof) -> Test
check s j p = check' s (j &&& p)

main :: IO Counts
main = runTestTT $ TestList
    [ check "excluded middle" excludedMiddle proofExcludedMiddle
    , check "trivial or" trivialOr proofTrivialOr
    , check "or commutativity" orCommutative proofOrCommutative
    , check "de morgan over or" deMorganOr proofDeMorganOr
    , check "de morgan over and" deMorganAnd proofDeMorganAnd
    , check "nested forall" nestedForAll proofNestedForAll
    , check "introduce with predicate" judgmentWithPredicateIntro proofJudgmentWithPredicateIntro
    , check "double predicate implication" doublePredicate proofDoublePredicate
    , check "exists forall -> forall exists" existsForAll proofExistsForAll
    , check "contraposition" contraposition proofContraposition

    -- toying with peano arithmetic
    , check' "zero has no predecessor" makeZeroHasNoPredecessor
    ]
