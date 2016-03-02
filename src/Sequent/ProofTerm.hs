module Sequent.ProofTerm
    ( Step(..)
    , Proof
    , contractionSuccedent, forAllSuccedent, forAllAntecedent
    , orElimLeftSuccedent , orElimRightSuccedent, negationSuccedent
    , negationAntecedent, orElimAntecedent, andElimSuccedent
    , andElimLeftAntecedent, andElimRightAntecedent, permuteSuccedent
    , permuteAntecedent
    ) where

import           Control.Monad (zipWithM)
import           Data.List     (intercalate)

import           Sequent.Env   (Env, Variable, evalEnv, fresh)

data Step
  = ContractionSuccedent
  | ForAllSuccedent (Variable -> Proof)
  | ForAllAntecedent Variable
  | OrElimLeftSuccedent
  | OrElimRightSuccedent
  | NegationSuccedent
  | NegationAntecedent
  | OrElimAntecedent Proof Proof
  | AndElimSuccedent Proof Proof
  | AndElimLeftAntecedent
  | AndElimRightAntecedent
  | PermuteSuccedent
  | PermuteAntecedent

instance Eq Step where
    a == b = evalEnv (eqStep a b)

instance Show Step where
    show = evalEnv . showStep

type Proof = [Step]

-- to show or test equality of two theorems we must be able to replace
-- quantifiers with contrete variables in order to eliminate functions
-- in our haskell representation of the theorem and explore the subtheorem

-- utility testing equality of two proof in a n
eqProofs :: Proof -> Proof -> Env Bool
eqProofs a b = and <$> zipWithM eqStep a b

eqStep :: Step -> Step -> Env Bool
eqStep ContractionSuccedent ContractionSuccedent     = return True
eqStep (ForAllAntecedent a) (ForAllAntecedent a')    = return (a == a')
eqStep OrElimLeftSuccedent OrElimLeftSuccedent       = return True
eqStep OrElimRightSuccedent OrElimRightSuccedent     = return True
eqStep NegationSuccedent NegationSuccedent           = return True
eqStep NegationAntecedent NegationAntecedent         = return True
eqStep AndElimLeftAntecedent AndElimLeftAntecedent   = return True
eqStep AndElimRightAntecedent AndElimRightAntecedent = return True
eqStep PermuteSuccedent PermuteSuccedent             = return True
eqStep PermuteAntecedent PermuteAntecedent           = return True
eqStep (ForAllSuccedent f) (ForAllSuccedent f') = do
    x <- fresh
    eqProofs (f x) (f' x)
eqStep (OrElimAntecedent l r) (OrElimAntecedent l' r') =
    (&&) <$> eqProofs l l' <*> eqProofs r r'
eqStep (AndElimSuccedent l r) (AndElimSuccedent l' r') =
    (&&) <$> eqProofs l l' <*> eqProofs r r'
eqStep _ _ = return False

showProofs :: Proof -> Env String
showProofs p = do
    s <- mapM showStep p
    return (intercalate ", " s)

showStep :: Step -> Env String
showStep ContractionSuccedent   = return "ContractionSuccedent"
showStep (ForAllAntecedent a)   = return ("ForAllAntecedent " ++ show a)
showStep OrElimLeftSuccedent    = return "OrElimLeftSuccedent"
showStep OrElimRightSuccedent   = return "OrElimRightSuccedent"
showStep NegationSuccedent      = return "NegationSuccedent"
showStep NegationAntecedent     = return "NegationAntecedent"
showStep AndElimLeftAntecedent  = return "AndElimLeftAntecedent"
showStep AndElimRightAntecedent = return "AndElimRightAntecedent"
showStep PermuteSuccedent       = return "PermuteSuccedent"
showStep PermuteAntecedent      = return "PermuteAntecedent"
showStep (ForAllSuccedent f) = do
    x <- fresh
    t <- showProofs (f x)
    return $ "ForAllSuccedent (" ++ show x ++ " -> " ++ t ++ ")"
showStep (OrElimAntecedent l r) = do
    showL <- showProofs l
    showR <- showProofs r
    return ("OrElimAntecedent (" ++ showL ++ ") (" ++ showR ++ ")")
showStep (AndElimSuccedent l r) =  do
    showL <- showProofs l
    showR <- showProofs r
    return ("AndElimSuccedent (" ++ showL ++ ") (" ++ showR ++ ")")


-- helpers

contractionSuccedent :: Proof
contractionSuccedent = [ContractionSuccedent]

forAllSuccedent :: (Variable -> Proof) -> Proof
forAllSuccedent f = [ForAllSuccedent f]

forAllAntecedent :: Variable -> Proof
forAllAntecedent a = [ForAllAntecedent a]

orElimLeftSuccedent :: Proof
orElimLeftSuccedent = [OrElimLeftSuccedent]

orElimRightSuccedent :: Proof
orElimRightSuccedent = [OrElimRightSuccedent]

negationSuccedent :: Proof
negationSuccedent = [NegationSuccedent]

negationAntecedent :: Proof
negationAntecedent = [NegationAntecedent]

orElimAntecedent :: Proof -> Proof -> Proof
orElimAntecedent l r = [OrElimAntecedent l r]

andElimSuccedent :: Proof -> Proof -> Proof
andElimSuccedent l r = [AndElimSuccedent l r]

andElimLeftAntecedent :: Proof
andElimLeftAntecedent = [AndElimLeftAntecedent]

andElimRightAntecedent :: Proof
andElimRightAntecedent = [AndElimRightAntecedent]

permuteSuccedent :: Proof
permuteSuccedent = [PermuteSuccedent]

permuteAntecedent :: Proof
permuteAntecedent = [PermuteAntecedent]
