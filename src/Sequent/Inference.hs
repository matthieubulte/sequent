module Sequent.Inference (check) where

import           Control.Applicative  (Alternative, empty, (<|>))
import           Control.Monad        (guard, mzero)
import           Control.Monad.Writer (tell)

import           Sequent.Check        (Check, liftEnv)
import           Sequent.Introduce    (introduce)
import qualified Sequent.Proof        as P
import           Sequent.Theorem      (Theorem ((:->)))
import qualified Sequent.Theorem      as T

-- TODO this seems to be a lot of work just to have monadplus-able functions
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
logStep step (antecedent, succedent) = do
    let longest [] = 0
        longest xs = maximum (fmap length xs)

    let ants  = fmap show antecedent
    let sucs  = fmap show succedent

    let l = max (longest ants) (longest sucs)

    tell $ unlines ants
        ++ "|" ++ replicate (l - 1) '-'
    tell $ unlines sucs
        ++ show step

    tell "\n"

    mzero


thenR :: Rule () -> InferenceRule -> Rule ()
thenR l r = l <|> Rule r

check :: InferenceRule
check = runRule $ Rule logStep
               `thenR` iAxiom
               `thenR` iContractionSuccedent
               `thenR` iContractionAntecedent
               `thenR` iWeakenSuccedent
               `thenR` iWeakenAntecedent
               `thenR` iForAllSuccedent
               `thenR` iForAllAntecedent
               `thenR` iForSomeSuccedent
               `thenR` iForSomeAntecedent
               `thenR` iOrElimLeftSuccedent
               `thenR` iOrElimRightSuccedent
               `thenR` iNegationSuccedent
               `thenR` iNegationAntecedent
               `thenR` iOrElimAntecedent
               `thenR` iAndElimSuccedent
               `thenR` iAndElimRightAntecedent
               `thenR` iAndElimLeftAntecedent
               `thenR` iImplicationAntecedent
               `thenR` iImplicationSuccedent
               `thenR` iPermuteSuccedent
               `thenR` iPermuteAntecedent
               `thenR` iRotateLeftAntecedent
               `thenR` iRotateLeftSuccedent

{-

----------------------- axiom
  Gamma, T |- T, _
-}
iAxiom :: InferenceRule
iAxiom P.Axiom (gammaA, t@(T.TTerm _):_) = guard (t `elem` gammaA)
iAxiom  _ _ = mzero

{-
   Gamma |- A, A, Delta
-------------------------- contract right
    Gamma |- A, Delta
-}
iContractionSuccedent :: InferenceRule
iContractionSuccedent (P.ContractionSuccedent rest) (gamma, a:delta) =
    check rest (gamma, a:a:delta)
iContractionSuccedent _ _ = mzero

{-
   Gamma, A, A |- Delta
-------------------------- contract left
    Gamma, A |- Delta
-}
iContractionAntecedent :: InferenceRule
iContractionAntecedent (P.ContractionAntecedent rest) (a:gamma, delta) =
    check rest (a:a:gamma, delta)
iContractionAntecedent _ _ = mzero

{-
      Gamma |- Delta
-------------------------- weaken right
    Gamma |- _, Delta
-}
iWeakenSuccedent :: InferenceRule
iWeakenSuccedent (P.WeakenSuccedent rest) (gamma, _:delta) =
    check rest (gamma, delta)
iWeakenSuccedent _ _ = mzero

{-
      Gamma |- Delta
-------------------------- weaken left
    Gamma, _ |- Delta
-}
iWeakenAntecedent :: InferenceRule
iWeakenAntecedent (P.WeakenAntecedent rest) (_:gamma, delta) =
    check rest (gamma, delta)
iWeakenAntecedent _ _ = mzero

{-
     Gamma |- A[y/x], Delta
-------------------------------- forall right
   Gamma |- forall x. A, Delta
-}
iForAllSuccedent :: InferenceRule
iForAllSuccedent (P.ForAllSuccedent t) (gamma, T.ForAll f:delta) = do
    y <- liftEnv introduce
    check (t y) (gamma, f y:delta)
iForAllSuccedent _ _ = mzero

{-
     Gamma, A[y/x] |- Delta
-------------------------------- forall left
   Gamma, forall x. A |- Delta
-}
iForAllAntecedent :: InferenceRule
iForAllAntecedent (P.ForAllAntecedent y rest) (T.ForAll f:gamma, delta) =
    check rest (f y:gamma, delta)
iForAllAntecedent _ _ = mzero

{-
     Gamma |- A[y/x], Delta
-------------------------------- forall right
   Gamma |- there exists x. A, Delta
-}
iForSomeSuccedent :: InferenceRule
iForSomeSuccedent (P.ForSomeSuccedent y rest) (gamma, T.ForSome f:delta) =
    check rest (gamma, f y:delta)
iForSomeSuccedent _ _ = mzero

{-
     Gamma, A[y/x] |- Delta
-------------------------------- forall left
   Gamma, there exists x. A |- Delta
-}
iForSomeAntecedent :: InferenceRule
iForSomeAntecedent (P.ForSomeAntecedent t) (T.ForSome f:gamma, delta) = do
    y <- liftEnv introduce
    check (t y) (f y:gamma, delta)
iForSomeAntecedent _ _ = mzero

{-
       Gamma |- A, Delta
----------------------------- right or-left
     Gamma |- A v _, Delta
-}
iOrElimLeftSuccedent :: InferenceRule
iOrElimLeftSuccedent (P.OrElimLeftSuccedent rest) (gamma, T.Or a _:delta) =
    check rest (gamma, a:delta)
iOrElimLeftSuccedent _ _ = mzero

{-
      Gamma |- B, Delta
----------------------------- right or-right
    Gamma |- _ v B, Delta
-}
iOrElimRightSuccedent :: InferenceRule
iOrElimRightSuccedent (P.OrElimRightSuccedent rest) (gamma, T.Or _ b:delta) =
    check rest (gamma, b:delta)
iOrElimRightSuccedent _ _ = mzero

{-
   Gamma, A |- Delta
----------------------- right not
   Gamma |- !A, Delta
-}
iNegationSuccedent :: InferenceRule
iNegationSuccedent (P.NegationSuccedent rest) (gamma, T.Not a:delta) =
    check rest (a:gamma, delta)
iNegationSuccedent _ _ = mzero

{-
   Gamma |- A, Delta
----------------------- left not
   Gamma, !A |- Delta
-}
iNegationAntecedent :: InferenceRule
iNegationAntecedent (P.NegationAntecedent rest) (T.Not a:gamma, delta) =
    check rest (gamma, a:delta)
iNegationAntecedent _ _ = mzero

{-
  Gamma, A |- Delta      Sigma, B |- Pi
----------------------------------------- left or
    Gamma, Sigma, A v B |- Delta, Pi
-}
iOrElimAntecedent :: InferenceRule
iOrElimAntecedent (P.OrElimAntecedent aProof bProof) (T.Or a b:gammaSigma, deltaPi) = do
    check aProof (a:gammaSigma, deltaPi)
    check bProof (b:gammaSigma, deltaPi)
iOrElimAntecedent _ _ = mzero

{-
  Gamma |- A, Delta      Sigma |- B, Pi
----------------------------------------- right and
    Gamma, Sigma |- A ^ B, Delta, Pi
-}
iAndElimSuccedent :: InferenceRule
iAndElimSuccedent (P.AndElimSuccedent aProof bProof) (gammaSigma, T.And a b:deltaPi) = do
    check aProof (gammaSigma, a:deltaPi)
    check bProof (gammaSigma, b:deltaPi)
iAndElimSuccedent _ _ = mzero

{-
    Gamma, A |- Delta
------------------------- left left and
   Gamma, A, _ |- Delta
-}
iAndElimLeftAntecedent :: InferenceRule
iAndElimLeftAntecedent (P.AndElimLeftAntecedent rest) (T.And a _:gamma, delta) =
    check rest (a:gamma, delta)
iAndElimLeftAntecedent _ _ = mzero

{-
    Gamma, B |- Delta
------------------------- right left and
   Gamma, _, B |- Delta
-}
iAndElimRightAntecedent :: InferenceRule
iAndElimRightAntecedent (P.AndElimRightAntecedent rest) (T.And _ b:gamma, delta) =
    check rest (b:gamma, delta)
iAndElimRightAntecedent _ _ = mzero

{-
    Gamma, A |- B, Delta
--------------------------- right implication
   Gamma |- A -> B, Delta
-}
iImplicationSuccedent :: InferenceRule
iImplicationSuccedent (P.ImplicationSuccedent rest) (gamma, a :-> b:delta) =
    check rest (a:gamma, b:delta)
iImplicationSuccedent _ _ = mzero

{-
    Sigma |- A, Pi   Gamma, B |- Delta
----------------------------------------- left implication
   Gamma, Sigma, A -> B |- Delta, Pi
-}
iImplicationAntecedent :: InferenceRule
iImplicationAntecedent (P.ImplicationAntecedent aProof bProof) (a :-> b:gammaSigma, deltaPi) = do
    check aProof (gammaSigma, a:deltaPi)
    check bProof (b:gammaSigma, deltaPi)
iImplicationAntecedent _ _ = mzero

{-
    Gamma |- B, A, Delta
--------------------------- right permute
    Gamma |- A, B, Delta
-}
iPermuteSuccedent :: InferenceRule
iPermuteSuccedent (P.PermuteSuccedent rest) (gamma, a:b:delta) =
    check rest (gamma, b:a:delta)
iPermuteSuccedent _ _ = mzero

{-
    Gamma, B, A |- Delta
--------------------------- left permute
    Gamma, A, B |- Delta
-}
iPermuteAntecedent :: InferenceRule
iPermuteAntecedent (P.PermuteAntecedent rest) (a:b:gamma, delta) =
    check rest (b:a:gamma, delta)
iPermuteAntecedent _ _ = mzero

{-
      A_2, ..., A_n, A_1 |- Delta
    -------------------------------- rotate right left
         A_1, ..., A_n |- Delta
-}
iRotateLeftAntecedent :: InferenceRule
iRotateLeftAntecedent (P.RotateLeftAntecedent rest) (as, delta) =
    check rest (rotate as, delta)
iRotateLeftAntecedent _ _ = mzero

{-
       Gamma |- A_2, ..., A_n, A_1
    -------------------------------- rotate right left
         Gamma |- A_1, ..., A_n
-}
iRotateLeftSuccedent :: InferenceRule
iRotateLeftSuccedent (P.RotateLeftSuccedent rest) (gamma, as) =
    check rest (gamma, rotate as)
iRotateLeftSuccedent _ _ = mzero

rotate :: [a] -> [a]
rotate [] = []
rotate (a:as) = as ++ [a]
