module Sequent.Inference (check) where

import           Control.Applicative  (Alternative, empty, (<|>))
import           Control.Monad        (MonadPlus, guard, mzero)
import           Control.Monad.Writer (tell)

import           Sequent.Check        (Check, fresh')
import qualified Sequent.ProofTerm    as P
import qualified Sequent.Theorem      as T


-- TODO this seems to be a lot of work just to have monoidal functions
newtype Rule a = Rule { runRule :: IRule a }
type IRule a = (P.Proof -> T.Judgment -> Check a)
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
              <|> Rule iContractionSuccedent
              <|> Rule iForAllSuccedent
              <|> Rule iForAllAntecedent
              <|> Rule iOrElimLeftSuccedent
              <|> Rule iOrElimRightSuccedent
              <|> Rule iNegationSuccedent
              <|> Rule iNegationAntecedent
              <|> Rule iOrElimAntecedent
              <|> Rule iAndElimSuccedent
              <|> Rule iAndElimRightAntecedent
              <|> Rule iAndElimLeftAntecedent
              <|> Rule iPermuteSuccedent
              <|> Rule iPermuteAntecedent

{-

----------------------- axiom
  Gamma, A |- A, Delta
-}
iAxiom :: InferenceRule
iAxiom [] (gammaA, a@(T.Var _):delta) = guard (a `elem` gammaA)
iAxiom _ _ = mzero

{-
   Gamma |- A, A, Delta
-------------------------- contract right
    Gamma |- A, Delta
-}
iContractionSuccedent :: InferenceRule
iContractionSuccedent (P.ContractionSuccedent:rest) (gamma, a:delta) =
    check rest (gamma, a:a:delta)
iContractionSuccedent _ _ = mzero

{-
     Gamma |- A[y/x], Delta
-------------------------------- forall right
   Gamma |- forall x. A, Delta
-}
iForAllSuccedent :: InferenceRule
iForAllSuccedent (P.ForAllSuccedent:rest) (gamma, T.ForAll f:delta) = do
    y <- fresh'
    check rest (gamma, f y:delta)
iForAllSuccedent _ _ = mzero

{-
     Gamma, A[y/x] |- Delta
-------------------------------- forall right
   Gamma |- forall x. A, Delta
-}
iForAllAntecedent :: InferenceRule
iForAllAntecedent (P.ForAllAntecedent y:rest) (gamma, T.ForAll f:delta) =
    check rest (gamma, f y:delta)
iForAllAntecedent _ _ = mzero

{-
       Gamma |- A, Delta
----------------------------- right or-left
     Gamma |- A v B, Delta
-}
iOrElimLeftSuccedent :: InferenceRule
iOrElimLeftSuccedent (P.OrElimLeftSuccedent:rest) (gamma, T.Or a b:delta) =
    check rest (gamma, a:delta)
iOrElimLeftSuccedent _ _ = mzero

{-
      Gamma |- B, Delta
----------------------------- right or-right
    Gamma |- A v B, Delta
-}
iOrElimRightSuccedent :: InferenceRule
iOrElimRightSuccedent (P.OrElimRightSuccedent:rest) (gamma, T.Or a b:delta) =
    check rest (gamma, b:delta)
iOrElimRightSuccedent _ _ = mzero

{-
   Gamma, A |- Delta
----------------------- right not
   Gamma |- !A, Delta
-}
iNegationSuccedent :: InferenceRule
iNegationSuccedent (P.NegationSuccedent:rest) (gamma, T.Not a:delta) =
    check rest (a:gamma, delta)
iNegationSuccedent _ _ = mzero

{-
   Gamma |- A, Delta
----------------------- left not
   Gamma, !A |- Delta
-}
iNegationAntecedent :: InferenceRule
iNegationAntecedent (P.NegationAntecedent:rest) (T.Not a:gamma, delta) =
    check rest (gamma, a:delta)
iNegationAntecedent _ _ = mzero

{-
  Gamma, A |- Delta      Sigma, B |- Pi
----------------------------------------- left or
    Gamma, Sigma, A v B |- Delta, Pi
-}
iOrElimAntecedent :: InferenceRule
iOrElimAntecedent [P.OrElimAntecedent aProof bProof] (T.Or a b:gammaSigma, deltaPi) = do
    check aProof (a:gammaSigma, deltaPi)
    check bProof (b:gammaSigma, deltaPi)
iOrElimAntecedent _ _ = mzero

{-
  Gamma |- A, Delta      Sigma |- B, Pi
----------------------------------------- right and
    Gamma, Sigma |- A ^ B, Delta, Pi
-}
iAndElimSuccedent :: InferenceRule
iAndElimSuccedent [P.AndElimSuccedent aProof bProof] (gammaSigma, T.And a b:deltaPi) = do
    check aProof (gammaSigma, a:deltaPi)
    check bProof (gammaSigma, b:deltaPi)
iAndElimSuccedent _ _ = mzero

{-
    Gamma, A |- Delta
------------------------- left left and
   Gamma, A, B |- Delta
-}
iAndElimLeftAntecedent :: InferenceRule
iAndElimLeftAntecedent (P.AndElimLeftAntecedent:rest) (T.And a b:gamma, delta) =
    check rest (a:gamma, delta)
iAndElimLeftAntecedent _ _ = mzero

{-
    Gamma, B |- Delta
------------------------- right left and
   Gamma, A, B |- Delta
-}
iAndElimRightAntecedent :: InferenceRule
iAndElimRightAntecedent (P.AndElimRightAntecedent:rest) (T.And a b:gamma, delta) =
    check rest (b:gamma, delta)
iAndElimRightAntecedent _ _ = mzero

{-
    Gamma |- B, A, Delta
--------------------------- right permute
    Gamma |- A, B, Delta
-}
iPermuteSuccedent :: InferenceRule
iPermuteSuccedent (P.PermuteSuccedent:rest) (gamma, a:b:delta) =
    check rest (gamma, b:a:delta)
iPermuteSuccedent _ _ = mzero

{-
    Gamma, B, A |- Delta
--------------------------- left permute
    Gamma, A, B |- Delta
-}
iPermuteAntecedent :: InferenceRule
iPermuteAntecedent (P.PermuteAntecedent:rest) (a:b:gamma, delta) =
    check rest (b:a:gamma, delta)
iPermuteAntecedent _ _ = mzero
