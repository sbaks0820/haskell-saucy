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
import Data.Map.Strict (member, empty, insert, Map, (!))
import qualified Data.Map.Strict as Map

forMseq_ xs f = sequence_ $ map f xs

data CastP2F a = CastP2F_cast a | CastP2F_ro Int deriving Show
data CastF2P a = CastF2P_OK | CastF2P_Deliver a | CastF2P_ro Bool deriving Show
data CastF2A a = CastF2A a | CastF2A_ro Bool deriving Show
data CastA2F a = CastA2F_Deliver PID a deriving Show

fMulticastAndCoin :: MonadFunctionalityAsync m (CastP2F t) =>
    Functionality (CastP2F t) (CastF2P t) (CastA2F t) (CastF2A t) Void Void m
fMulticastAndCoin (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
    let sid = ?sid :: SID
    let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "fMulticastAndCoin" $ snd sid

    coinFlips <- newIORef (empty :: Map Int Bool)

    if not $ member pidS ?crupt then
        -- Only activated by the designated sender
        fork $ forever $ do
            (pid, m) <- readChan p2f
            case m of
                CastP2F_ro x -> do
                    cf <- readIORef coinFlips
                    if not $ member x cf then do
                        b <- ?getBit
                        modifyIORef coinFlips $ Map.insert x b 
                        writeChan f2p (pid, CastF2P_ro b)
                    else do
                        b <- readIORef coinFlips >>= return . (! x)
                        writeChan f2p (pid, CastF2P_ro b)
                CastP2F_cast x ->
                    if pid == pidS then do
                        ?leak m
                        forMseq_ parties $ \pidR -> do
                            eventually $ writeChan f2p (pidR, CastF2P_Deliver x)
                        writeChan f2p (pidS, CastF2P_OK)
                    else error "multicast activated not by sender"
    else do
        delivered <- newIORef (empty :: Map PID ())
        fork $ forever $ do
            CastA2F_Deliver pidR m <- readChan a2f
            del <- readIORef delivered
            if member pidR del then return ()
            else do
                modifyIORef delivered $ Map.insert pidR ()
                writeChan f2p (pidR, CastF2P_Deliver m)
    return ()


testEnvMulticastCoin z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let sid = ("sidTestEnvMulticastCoin", show (("Alice", "Bob", "Charlie", "Mary"), ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty 

    fork $ forever $ do
        (pid, (s, m)) <- readChan p2z
        -- liftIO $ putStrLn $ "Z: party[" ++ pid ++ "] output " ++ show m
        ?pass

    fork $ forever $ do 
        m <- readChan a2z
        liftIO $ putStrLn $ "Z: a sent "

    () <- readChan pump
    writeChan z2p ("Alice", (("sidX", ""), (CastP2F_ro 0)))

main :: IO String
main = runITMinIO 120 $ execUC testEnvMulticastCoin idealProtocol (bangFAsync fMulticastAndCoin) dummyAdversary
                    
