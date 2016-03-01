module Main where

import           Sequent (checkExcludedMiddle, checkOrCommutative,
                          checkTrivialOr)

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
