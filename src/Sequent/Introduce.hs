module Sequent.Introduce
    ( Introduce
    , introduce
    , runIntros
    ) where

import           Sequent.Env (EnvT)

-- Introduce represent a value that can be generated in an environment
-- it can actually only be variables, but we want to be able to generate
-- several variables to express a proof and thus need to be able to generate
-- tuples of fresh variables.
class Introduce a where
  introduce :: (Monad m) => EnvT m a

instance Introduce () where
  introduce = return ()

instance (Introduce a, Introduce b) => Introduce (a, b) where
    introduce = (,) <$> introduce <*> introduce

instance (Introduce a, Introduce b, Introduce c) => Introduce (a, b, c) where
    introduce = (,,) <$> introduce <*> introduce <*> introduce

instance (Introduce a, Introduce b, Introduce c, Introduce d) => Introduce (a, b, c, d) where
    introduce = (,,,) <$> introduce <*> introduce <*> introduce <*> introduce

instance (Introduce a, Introduce b, Introduce c, Introduce d, Introduce e) => Introduce (a, b, c, d, e) where
    introduce = (,,,,) <$> introduce <*> introduce <*> introduce <*> introduce <*> introduce
-- Create the fresh variable required for a theorem to be expressed
runIntros :: (Monad m, Introduce a) => (a -> b) -> EnvT m b
runIntros f = f <$> introduce
