module Main where

import           Sequent (checkExcludedMiddle, checkTrivialOr)

main :: IO ()
main = do
    let (result, trace) = checkTrivialOr
    let (result', trace') = checkExcludedMiddle

    putStrLn ("Trivial or success: " ++ maybe "No" (const "Yes") result)
    putStrLn ("Trace:\n" ++ trace)

    putStrLn "--------------------------------"

    putStrLn ("Excluded middle success: " ++ maybe "No" (const "Yes") result')
    putStrLn ("Trace:\n" ++ trace')
