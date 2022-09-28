 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures
  #-} 

module TestTools where

import ProcessIO
import StaticCorruptions

import Safe
import Control.Concurrent.MonadIO 
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.List (elemIndex, delete)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

--let iogenerate = liftIO $ generate 

selectPIDs :: (MonadIO m) => [PID] -> m [PID]
selectPIDs pids = do
    s_pids <- liftIO $ (generate $ shuffle pids)
    n <- liftIO $ (generate $ choose (1, length pids))
    let r_pids :: [PID] = take n s_pids
    return r_pids

--{-- Prop Envronment Class --}
--type MonadPropEnvironment m a =
--	(MonadITM m,
--	 ?pass :: m ())
--
--type PropEnvironment p2z z2p a2z z2a f2z z2f outz cmd m = MonadPropEnvironment m => Chan SttCrupt_SidCrupt -> (Chan (PID, p2z), Chan (PID, z2p)) -> (Chan a2z, Chan z2a) -> (Chan f2z, Chan z2f) -> Chan () -> Chan (outz, [cmd]) -> m ()
--
--runPropEnv :: MonadEnvironment m =>
--				(MonadPropEnvironment m a => Environment p2z z2p a2z z2a f2z z2f outz m)
--			-> Environment p2z z2p a2z z2a f2z z2f (a, outz) m
--runPropEnv z (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp m = do
	
