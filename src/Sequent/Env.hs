{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UndecidableInstances       #-}

module Sequent.Env
    ( Variable
    , EnvT, evalEnvT
    , Env, evalEnv
    , fresh
    ) where

import           Control.Monad.State.Lazy (MonadState, StateT, evalStateT, get,
                                           modify)
import           Control.Monad.Trans      (MonadTrans)
import           Control.Monad.Writer     (MonadWriter)
import           Data.Functor.Identity    (Identity, runIdentity)

-- Wrapper around an integer, a variable can only be created using the
-- fresh function to avoid name collisions.
newtype Variable = Variable Int deriving (Eq)

instance Show Variable where
    show (Variable x) = "x_" ++ show x

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

fresh :: (Monad m) => EnvT m Variable
fresh = do
    x <- get
    modify succ
    return (Variable x)
