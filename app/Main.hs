module Main where

import           Sequent (checkDeMorganAnd, checkDeMorganOr,
                          checkExcludedMiddle, checkNestedForAll,
                          checkOrCommutative, checkTheoremDoublePredicate,
                          checkTheoremWithPredicateIntro, checkTrivialOr)

showCheck :: String -> (Maybe (), String) -> IO ()
showCheck theorem (result, trace) = do
    putStrLn (theorem ++ "\n")
    putStrLn trace
    putStrLn (maybe "Failed" (const "Succeeded") result)
    putStrLn "--------------------------------"

main :: IO ()
main = do
    showCheck "excluded middle" checkExcludedMiddle
    showCheck "trivial or" checkTrivialOr
    showCheck "or commutativity" checkOrCommutative
    showCheck "de morgan over or" checkDeMorganOr
    showCheck "de morgan over and" checkDeMorganAnd
    showCheck "nested forall" checkNestedForAll
    showCheck "introduce with predicate" checkTheoremWithPredicateIntro
    showCheck "double predicate implication" checkTheoremDoublePredicate
