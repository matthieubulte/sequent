{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Sequent.Check
    ( CheckT
    , Check
    , evalCheck
    , evalCheckT
    , liftEnv) where

import           Control.Applicative       (Alternative)
import           Control.Monad             (MonadPlus)
import           Control.Monad.Trans       (MonadTrans, lift)
import           Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import           Control.Monad.Writer      (MonadWriter, WriterT, listen, pass,
                                            runWriterT, tell)
import           Data.Functor.Identity     (Identity, runIdentity)

import           Sequent.Env               (EnvT, evalEnvT)

-- Wrapper around String to add a new line between two non-empty lines
-- when appending them together
newtype Lines = Lines { unLines :: String }
    deriving (Eq)

instance Show Lines where
    show = unLines

instance Monoid Lines where
    mempty = Lines ""
    mappend a b
        | b == mempty = a
        | a == mempty = b
        | otherwise   = Lines (unLines a ++ "\n" ++ unLines b)

-- Everything that is needed when checking a proof:
--      + MaybeT to be able to terminate an incorrect proof
--      + EnvT to generate fresh variables
--      + WriterT to log the steps of the proof
-- TODO replace MaybeT with some instance of MonadError ?
newtype CheckT m a = CheckT { runCheckT :: MaybeT (WriterT Lines (EnvT m)) a }
    deriving ( Functor
             , Applicative
             , Alternative
             , MonadPlus
             , Monad)

type Check = CheckT Identity

-- Write a custom instance to be able to use the "tell :: String -> _" interface
-- from the outside, keeping the Lines type hidden and have a custom mappend
instance Monad m => MonadWriter String (CheckT m) where
    tell   = CheckT . tell . Lines
    listen = CheckT . fmap (fmap unLines) . listen . runCheckT
    pass = CheckT . pass . fmap (fmap (\f -> Lines . f . unLines)) . runCheckT

-- The MonadTrans instance can't be automatically derived because of the StateT
-- in the EnvT. See (https://www.reddit.com/r/haskell/comments/3mrkwe/issue_deriving_monadtrans_for_chained_custom/)
instance MonadTrans CheckT where
    lift = CheckT . lift . lift . lift

evalCheckT :: (Monad m) => CheckT m a -> m (Maybe a, String)
evalCheckT = fmap (fmap unLines) . evalEnvT . runWriterT . runMaybeT . runCheckT

evalCheck :: Check a -> (Maybe a, String)
evalCheck = runIdentity . evalCheckT

liftEnv :: (Monad m) => EnvT m a -> CheckT m a
liftEnv = CheckT . lift . lift
