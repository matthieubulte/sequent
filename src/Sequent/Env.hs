{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UndecidableInstances       #-}

module Sequent.Env
    ( EnvT, evalEnvT
    , Env, evalEnv
    , next
    ) where

import           Control.Monad.State.Lazy (MonadState, StateT, evalStateT, get,
                                           modify)
import           Control.Monad.Trans      (MonadTrans)
import           Control.Monad.Writer     (MonadWriter)
import           Data.Functor.Identity    (Identity, runIdentity)

-- TODO replace with a SupplyT ?
newtype EnvT m a = EnvT { runEnv :: StateT Int m a }
    deriving ( Functor
             , Applicative
             , Monad
             , MonadTrans
             , MonadState Int
             , MonadWriter w)

type Env = EnvT Identity

evalEnvT :: (Monad m) => EnvT m a -> m a
evalEnvT env = evalStateT (runEnv env) 0

evalEnv :: Env a -> a
evalEnv = runIdentity . evalEnvT

next :: (Monad m) => EnvT m Int
next = do
    x <- get
    modify succ
    return x
