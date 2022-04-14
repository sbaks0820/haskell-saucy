 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures
  #-} 

module ABA where

import ProcessIO
import StaticCorruptions
import Async
import Multisession

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data CastP2F a = CastP2F_cast a | CastP2F_ro Int deriving Show
data CastF2P a = CastF2P_OK | CastF2P_Deliver a | CastF2P_ro Bool deriving Sho
data CastF2A a = CastF2A a deriving Show
data CastA2F a = CastA2F_Deliver PID a deriving Show

fMulticastAndCoin :: MonadFunctionalityAsync m t =>
	Functionality (CastP2F t) (CastF2P t) (CastA2F t) (CastF2A t) Void Void m
fMulticastAndCoin (p2f, f2p), (a2f, f2a), (z2f, f2z) = do
	let sid = ?sid :: SID
	let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "fMulticastAndCoin" $ snd sid
	
	
