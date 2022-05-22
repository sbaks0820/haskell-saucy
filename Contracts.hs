{-# LANGUAGE Rank2Types, ImplicitParams, ConstraintKinds,
             ScopedTypeVariables
  #-} 

{- 

 -}

module Contracts where

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_, replicateM)
import System.Random

import ProcessIO
import StaticCorruptions

import Data.IORef.MonadIO
import Data.Map.Strict hiding (drop,splitAt)

type MonadContract m = (MonadITM m)

type Contract p2f f2p f2c c2f emit m = MonadContract m => (Chan (PID, p2f), Chan (PID, f2p)) -> (Chan f2c, Chan c2f) -> Chan emit -> m ()


