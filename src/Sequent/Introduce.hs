module Sequent.Introduce (runIntros, Introduce) where

import           Sequent.Env     (EnvT, Variable, evalEnv, fresh)
import           Sequent.Theorem (Theorem)

-- Introduce represent a value that can be generated in an environment
-- it can actually only be variables, but we want to be able to generate
-- several variables to express a proof and thus need to be able to generate
-- tuples of fresh variables.
class Introduce a where
  introduce :: (Monad m) => EnvT m a

instance Introduce () where
  introduce = return ()

instance Introduce Variable where
    introduce = fresh

instance (Introduce a, Introduce b) => Introduce (a, b) where
    introduce = (,) <$> introduce <*> introduce

instance (Introduce a, Introduce b, Introduce c) => Introduce (a, b, c) where
    introduce = (,,) <$> introduce <*> introduce <*> introduce

-- Create the fresh variable required for a theorem to be expressed
runIntros :: (Introduce a) => (a -> b) -> b
runIntros f = evalEnv (f <$> introduce)
