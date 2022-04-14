{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds, PartialTypeSignatures
  #-}

module BrachaBroadcast where

import ProcessIO
import StaticCorruptions
import Safe

import Control.Concurrent.MonadIO
import Control.Monad (forever)
import Control.Monad.State (lift)
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map

import OptionallyLeak

data Void

data BrachaP2F a = BrachaP2F_Input a deriving Show
data BrachaF2P a = BrachaF2P_Output a | BrachaF2P_OK deriving Show

-- fBracha :: MonadLeak m t => 
-- 	Functionality BrachaP2F
fBracha (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
    let sid = ?sid :: SID
    let (pidD :: PID, parties :: [PID], sssid :: String) = readNote "fBracha" $ snd sid 
    liftIO $ putStrLn $ "F: Dealer[" ++ pidD ++ "] parties " ++ show parties
    fork $ do 
        mp <- readChan p2f
        let (pid, BrachaP2F_Input x) = mp
        
        -- only the dealer gives input
        if pid == pidD
        then do
            leak x 
            forM_ parties $ \pid -> do
                optionally $ do 
                    writeChan f2p $ (pid, BrachaF2P_Output x)
            writeChan f2p (pid, BrachaF2P_OK)
        else do
            error "Only the dealer can give input"
    return () 


testEnvBrachaBenign z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let sid = ("sidTestEnvMapBenign", show ("Alice", ["Alice", "Bob", "Charlie", "Mary"], ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty
    
    fork $ forever $ do
        (pid, m) <- readChan p2z
        liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
        ?pass
    
    fork $ forever $ do
        m <- readChan a2z
        liftIO $ putStrLn $ "Z: a sent "
        ?pass

    () <- readChan pump
    writeChan z2p ("Alice", BrachaP2F_Input 1)

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Through LeakA2F_Get

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 3

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

    () <- readChan pump
    writeChan outp () 

test :: IO ()
test = runITMinIO 120 $ execUC testEnvBrachaBenign idealProtocol (runOptLeak fBracha) dummyAdversary
       

