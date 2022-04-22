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
import Control.Monad (forever, forM, liftM)
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
        liftIO $ putStrLn $ "Z: party[" ++ pid ++ "] output " ++ show m
        ?pass

    fork $ forever $ do 
        m <- readChan a2z
        liftIO $ putStrLn $ "Z: a sent " ++ show m 

    let sid1 :: SID = ("sidX", show ("Alice", ["Alice", "Bob", "Charlie", "Mary"], ""))

    () <- readChan pump
    writeChan z2p ("Alice", (sid1, (CastP2F_ro 0)))

    () <- readChan pump
    writeChan z2p ("Alice", (sid1, (CastP2F_cast 1)))

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

testMulticastAndCoin :: IO String
testMulticastAndCoin = runITMinIO 120 $ execUC testEnvMulticastCoin idealProtocol (runAsyncF $ bangFAsync fMulticastAndCoin) dummyAdversary

data ABACast = AUX Int Bool | EST Int Bool

sBroadcast round (bit :: Bool) (f2p, p2f) binptr shouldBCast = do
    modifyIORef binptr $ Map.insert bit False
    vCount <- newIORef 0 
    let firstThreshold = False
    let secondThreshold = True
          
    let sidmycast :: SID = (show ("sbcast", ?pid, round, bit), show (?pid, ?parties, ""))

    if shouldBCast then do
        writeChan p2f (sidmycast, CastP2F_cast (EST round bit))
        -- (ssid :: SID, CastF2P_OK) <- readChan f2p
        (pidS :: PID, CastF2P_OK) <- readChan f2p
        require (pidS == ?pid) "OK from wrong fMulticast session"
    else 
        return ()
   
    fork $ forever $ do
        (from :: PID, CastF2P_Deliver (EST r b)) <- readChan f2p
        if (b == bit) && (from /= ?pid)  then do
            modifyIORef vCount $ (+) 1
            if (vCount == (?t + 1)) then do
                writeChan p2f (sidmycast, CastP2F_cast (EST round bit)) 
                (pidS :: PID, CastF2P_OK) <- readChan f2p
                require (pidS == ?pid) "OK from wrong fMulticast session"
            else if vCount == ((?t * 2) + 1) then
                modifyIORef binptr $ Map.insert bit True
            else
                return ()
        else return ()
    return ()
        

data ABAF2P = ABAF2P_Out Bool deriving Show

--data CastP2F a = CastP2F_cast a | CastP2F_ro Int deriving Show
--data CastF2P a = CastF2P_OK | CastF2P_Deliver a | CastF2P_ro Bool deriving Show
--data CastF2A a = CastF2A a | CastF2A_ro Bool deriving Show
--data CastA2F a = CastA2F_Deliver PID a deriving Show

protABA :: MonadProtocol m =>
    Protocol Bool ABAF2P (SID, CastF2P ABACast) (SID, CastP2F ABACast) m
protABA (z2p, p2z) (f2p, p2f) = do
    let sid = ?sid :: SID
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "fMulticast" $ snd sid 

    view <- newIORef (empty :: Map Int [Bool])
    binptr <- newIORef (empty :: Map Bool Bool)

    -- read message and route to either sBroadcast or to the main protocol
    -- manyS <- newIORef (empty :: Map Int (Chan (PID, (CastF2P ABACast))))
    manyS <- newIORef (empty :: Map (SID, int, Bool) (Chan (PID, (CastF2P ABACast))))
    toMain <- newChan


    let newSBcastChan s r b d = do
                c <- newChan
                modifyIORef d $ Map.insert (s, r, b) c
                return c

    let getSChan s r b d = readIORef manyS >>= return . (! (s, r, b))
    let ssidFromParams r b = (show ("sbcast", ?pid, r, b), show (?pid, ?parties, ""))

    fork $ forever $ do
        (s, m) <- readChan f2p
        let (pidS :: PID, fParties :: [PID], ssid :: String) = readNote "fMulticastAndCoin" $ snd s
        let (sstring :: String, _pidS :: PID, _round :: Int, _bit :: Bool) = readNote "" $ fst s

        case m of 
            CastF2P_Deliver (EST r b) -> do
                _toS <- getSChan s r b manyS
                writeChan _toS (pidS, m)
            CastF2P_Deliver (AUX r b) -> do
                _toS <- getSChan s r b manyS
                writeChan toMain (pidS, m)
            CastF2P_OK -> do
                if sstring == "sbcast" then do
                    _toS <- getSChan s _round _bit manyS
                    writeChan _toS (pidS, m)
                else
                    writeChan toMain (pidS, m)
            _ -> 
                writeChan toMain (?pid, m)
    

    v <- readChan z2p
    s <- liftM not v
    supportCoin <- newIORef False 
    newSBcastChan (ssidFromParams 1 s) 1 s manyS 
    c <- getSChan (ssidFromParams 1 s) 1 s manyS
    
    fork $ do
        sBroadcast 1 s (c, p2f) binptr False

    return () 
