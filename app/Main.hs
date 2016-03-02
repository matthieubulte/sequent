module Main where

import           Sequent (checkDeMorganAnd, checkDeMorganOr,
                          checkExcludedMiddle, checkNestedForAll,
                          checkOrCommutative, checkTrivialOr)

showCheck :: String -> (Maybe (), String) -> IO ()
showCheck theorem (result, trace) = do
    putStrLn ("'" ++ theorem ++ "' success: " ++ maybe "No" (const "Yes") result)
    putStrLn ("Trace:\n" ++ trace)

    putStrLn "--------------------------------"

main :: IO ()
main = do
    showCheck "excluded middle" checkExcludedMiddle
    showCheck "trivial or" checkTrivialOr
    showCheck "or commutativity" checkOrCommutative
    showCheck "de morgan over or" checkDeMorganOr
    showCheck "de morgan over and" checkDeMorganAnd
    showCheck "nested forall" checkNestedForAll
