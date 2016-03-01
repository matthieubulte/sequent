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
import           Control.Monad.Trans      (MonadTrans, lift)
import           Control.Monad.Writer     (MonadWriter)
import           Data.Functor.Identity    (Identity, runIdentity)

newtype Variable = Variable Int deriving (Eq)

instance Show Variable where
    show (Variable x) = "x_" ++ show x

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
    modify (+1)
    return (Variable x)
