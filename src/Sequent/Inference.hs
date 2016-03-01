module Sequent.Inference (check) where

import           Control.Applicative  (Alternative, empty, (<|>))
import           Control.Monad        (MonadPlus, guard, mzero)
import           Control.Monad.Writer (tell)

import           Sequent.Check        (Check, fresh')
import qualified Sequent.ProofTerm    as P
import qualified Sequent.Theorem      as T


-- TODO this seems to be a lot of work just to have monoidal functions
newtype Rule a = Rule { runRule :: IRule a }
type IRule a = (P.Proof -> T.Theorem -> Check a)
type InferenceRule = IRule ()

instance Functor Rule where
    fmap f (Rule g) = Rule (\s t -> fmap f (g s t))

instance Applicative Rule where
    pure x = Rule (\_ _ -> return x)
    (Rule f) <*> (Rule g) = Rule (\s t -> f s t <*> g s t)

instance Alternative Rule where
    empty = Rule (\_ _ -> empty)
    (Rule f) <|> (Rule g) = Rule (\s t -> f s t <|> g s t)


logStep :: InferenceRule
logStep [] theorem = tell (show theorem) >> mzero
logStep (step:_) theorem = tell (show (step, theorem)) >> mzero

check :: InferenceRule
check = runRule $ Rule logStep
              <|> Rule iAxiom
              <|> Rule iContractionRight
              <|> Rule iForAllRight
              <|> Rule iLeftOrElimRight
              <|> Rule iRightOrElimRight
              <|> Rule iNegationRight
              <|> Rule iOrElimLeft
              <|> Rule iPermuteRight

{-

----------------------- axiom
  Gamma, A |- A, Delta
-}
iAxiom :: InferenceRule
iAxiom [] (gammaA, a:delta) = guard (a `elem` gammaA)
iAxiom _ _ = mzero

{-
   Gamma |- A, A, Delta
-------------------------- contract right
    Gamma |- A, Delta
-}
iContractionRight :: InferenceRule
iContractionRight (P.ContractionRight:rest) (gamma, a:delta) =
    check rest (gamma, a:a:delta)
iContractionRight _ _ = mzero

{-
     Gamma |- A[y/x], Delta
-------------------------------- forall right
   Gamma |- forall x. A, Delta
-}
iForAllRight :: InferenceRule
iForAllRight (P.ForAllRight:rest) (gamma, T.ForAll f:delta) = do
    y <- fresh'
    check rest (gamma, f y:delta)
iForAllRight _ _ = mzero

{-
       Gamma |- A, Delta
----------------------------- right or-left
     Gamma |- A v B, Delta
-}
iLeftOrElimRight :: InferenceRule
iLeftOrElimRight (P.LeftOrElimRight:rest) (gamma, T.Or a b:delta) =
    check rest (gamma, a:delta)
iLeftOrElimRight _ _ = mzero

{-
      Gamma |- B, Delta
----------------------------- right or-right
    Gamma |- A v B, Delta
-}
iRightOrElimRight :: InferenceRule
iRightOrElimRight (P.RightOrElimRight:rest) (gamma, T.Or a b:delta) =
    check rest (gamma, b:delta)
iRightOrElimRight _ _ = mzero

{-
   Gamma, A |- Delta
----------------------- left not
   Gamma |- !A, Delta
-}
iNegationRight :: InferenceRule
iNegationRight (P.NegationRight:rest) (gamma, T.Not a:delta) =
    check rest (a:gamma, delta)
iNegationRight _ _ = mzero

{-
    Gamma |- B, A, Delta
--------------------------- right permute
    Gamma |- A, B, Delta
-}
iPermuteRight :: InferenceRule
iPermuteRight (P.PermuteRight:rest) (gamma, a:b:delta) =
    check rest (gamma, b:a:delta)
iPermuteRight _ _ = mzero

{-
Gamma, A |- Delta      Sigma, B |- Pi
------------------------------------- left or
  Gamma, Sigma, A v B |- Delta, Pi
-}
iOrElimLeft :: InferenceRule
iOrElimLeft [P.OrElimLeft aProof bProof] (T.Or a b:gammaSigma, deltaPi) = do
    check aProof (a:gammaSigma, deltaPi)
    check bProof (b:gammaSigma, deltaPi)
iOrElimLeft _ _ = mzero
