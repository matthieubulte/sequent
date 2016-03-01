{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Sequent.Check
    ( CheckT
    , Check
    , evalCheck
    , evalCheckT
    , fresh') where

import           Control.Applicative       (Alternative)
import           Control.Monad             (MonadPlus)
import           Control.Monad.Trans       (MonadTrans, lift)
import           Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import           Control.Monad.Writer      (MonadWriter, WriterT, listen, pass,
                                            runWriterT, tell)
import           Data.Functor.Identity     (Identity, runIdentity)

import           Sequent.Env               (EnvT, Variable, evalEnvT, fresh)

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


-- TODO replace MaybeT with some instance of MonadError ?
-- Everything that is needed when checking a proof
newtype CheckT m a = CheckT { runCheckT :: MaybeT (EnvT (WriterT Lines m)) a }
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

instance MonadTrans CheckT where
    lift = CheckT . lift . lift . lift

evalCheckT :: (Monad m) => CheckT m a -> m (Maybe a, String)
evalCheckT = fmap (fmap unLines) . runWriterT . evalEnvT . runMaybeT . runCheckT

evalCheck :: Check a -> (Maybe a, String)
evalCheck = runIdentity . evalCheckT

-- TODO does this belong here / make sense?
fresh' :: (Monad m) => CheckT m Variable
fresh' = (CheckT . lift) fresh
