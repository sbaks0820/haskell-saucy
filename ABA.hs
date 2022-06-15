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
    
    let print x = do
            liftIO $ putStrLn $ x


    coinFlips <- newIORef (empty :: Map Int Bool)

    if not $ member pidS ?crupt then
        -- Only activated by the designated sender
        fork $ forever $ do
            (pid, m) <- readChan p2f
            -- print "[fMulticastAndCoin] received message on p2f" 
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
                        --print ("[fMulticastAndCoin, sender:" ++ (show pidS) ++ "]")
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
    writeChan z2p ("Alice", ClockP2F_Through (sid1, (CastP2F_ro 0)))

    () <- readChan pump
    writeChan z2p ("Alice", ClockP2F_Through (sid1, (CastP2F_cast 1)))

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

testMulticastAndCoin :: IO String
testMulticastAndCoin = runITMinIO 120 $ execUC testEnvMulticastCoin idealProtocol (runAsyncF $ bangFAsync fMulticastAndCoin) dummyAdversary

data ABACast = AUX Int Bool | EST Int Bool deriving Show

sBroadcast :: (MonadIO m, MonadITM m) => 
    Int -> PID -> [PID] -> Int -> Bool -> Chan (PID, CastF2P ABACast) -> Chan (SID, CastP2F ABACast) -> Chan () -> Chan () -> IORef (Map Bool Bool) -> Bool -> m () -> m ()
sBroadcast tThreshold pid parties round bit f2p p2f okChan toMainChan binptr shouldBCast pass = do
    --liftIO $ putStrLn $ "sBroadcast: Party[" ++ pid ++ "] round " ++ show round ++ " bit " ++ show bit
    --modifyIORef binptr $ Map.insert bit False
    vCount <- newIORef 0
    let firstThreshold = False
    let secondThreshold = True
          
    let sidmycast :: SID = (show ("sbcast", pid, round, bit), show (pid, parties, ""))

    if shouldBCast then do
        writeChan p2f (sidmycast, CastP2F_cast (EST round bit))
        -- (ssid :: SID, CastF2P_OK) <- readChan f2p
        --(pidS :: PID, CastF2P_OK) <- Just $ readChan f2p
        --readChan f2p
        readChan okChan
        -- return ()
        -- require (pidS == pid) "OK from wrong fMulticast session"
        pass
    else 
        return ()

    --liftIO $ putStrLn $ "sBroadcast starting main loop"

    fork $ forever $ do
        -- (from :: PID, CastF2P_Deliver (EST r b)) <- readChan f2p
        (from, m) <- readChan f2p
        liftIO $ putStrLn $ "Got something at sBCast [" ++ show pid ++ "] msg " ++ show m 
        case m of
            CastF2P_Deliver (EST r b) -> do
                if (b == bit) && (from /= pid)  then do
                    liftIO $ putStrLn $ ("sBroadcast [" ++ show pid ++ "] got someone elses message for the same bit [" ++ show b ++ "]")
                    modifyIORef vCount $ (+) 1
                    _v <- readIORef vCount
                    if (_v == (tThreshold + 1)) then do
                        writeChan p2f (sidmycast, CastP2F_cast (EST round bit))
                        --(pidS :: PID, CastF2P_OK) <- readChan f2p
                        -- require (pidS == pid) "OK from wrong fMulticast session"
                        --return ()
                        readChan okChan
                    else if _v == ((tThreshold * 2) + 1) then do
                        modifyIORef binptr $ Map.insert bit True
                        writeChan toMainChan ()
                    else do
                        liftIO $ putStrLn $ "sBCast [" ++ show pid ++ "] nothing to do yet"
                        pass
                        --return ()
                else pass
            _ -> pass 
    return ()
        

data ABAF2P = ABAF2P_Out Bool deriving Show

protABA :: MonadAsyncP m =>
    Protocol (ClockP2F Bool) ABAF2P (SID, CastF2P ABACast) (SID, CastP2F ABACast) m
protABA (z2p, p2z) (f2p, p2f) = do
    let sid = ?sid :: SID
    let pid = ?pid :: PID
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "fMulticast" $ snd sid 

    view <- newIORef (empty :: Map Int [Bool])
    binptr <- newIORef (empty :: Map Bool Bool)
    modifyIORef binptr $ Map.insert False False
    modifyIORef binptr $ Map.insert True False

    

    -- read message and route to either sBroadcast or to the main protocol
    -- manyS <- newIORef (empty :: Map Int (Chan (PID, (CastF2P ABACast))))
    manyS <- newIORef (empty :: Map (SID, Int, Bool) (Chan (PID, (CastF2P ABACast))))
    manyOK <- newIORef (empty :: Map (SID, Int, Bool) (Chan ()))
    manyStoMain <- newIORef (empty :: Map Int (Chan ()))
    toMain <- newChan
    toMainOK <- newChan


    -- create 2 channels for SBroadcast, one for messages
    -- and one for OK from fMulticast
    let newSBcastChan s r b ms mok m2m = do
                _S <- newChan
                _OK <- newChan
                _toMain <- newChan
                modifyIORef ms $ Map.insert (s, r, b) _S
                modifyIORef mok $ Map.insert (s, r, b) _OK
                modifyIORef m2m $ Map.insert r _toMain
                return (_S,_OK, _toMain)

    -- get the message channel for the SBroadcast instance
    let getSChan s r b d = do
            readIORef manyS >>= return . (! (s, r, b))

    -- get the OK channel for the SBroadcast instance
    let getOKChan s r b d = do 
            readIORef manyOK >>= return . (! (s, r, b))

    -- Compute the ssid from the broadcast parameters
    -- Identify messages by sid, round, and bit of SBroadcast
    let ssidFromParams r b = (show ("sbcast", ?pid, r, b), show (?pid, parties, ""))

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
                    _toOK <- getOKChan s _round _bit manyOK
                    writeChan _toOK ()
                else
                    writeChan toMainOK ()
            _ -> 
                writeChan toMain (?pid, m)
   
    let newSBCast v shouldBroadcast = do
            (sf2p, sok, stomain) <- newSBcastChan (ssidFromParams 1 v) 1 v manyS manyOK manyStoMain
            sBroadcast t pid parties 1 v sf2p p2f sok stomain binptr shouldBroadcast ?pass

    let round = 0
    
    -- on input propose(v) from Z:
    msg <- readChan z2p
    case msg of
        ClockP2F_Pass -> error "shouldn't be passing anything"
        ClockP2F_Through v -> do
            s <- return (not v)
            supportCoin <- (return False)
            newSBCast s False   

            fork $ forever $ do
                liftIO $ putStrLn $ "new round" 
                let round = round + 1
                --m <- readChan z2p
                newSBCast (not s) (not supportCoin)

                -- wait for one of the processes to write to the main thread
                -- saying that they set binptr[b] = True
                -- ?pass
                s2MainChan <- readIORef manyStoMain >>= return . (! round) 
                () <- readChan s2MainChan

                -- set w for broadcast
                b0 <- readIORef binptr >>= return . (! False)
                b1 <- readIORef binptr >>= return . (! True)

                let w = if supportCoin
                        then s
                        else if b0
                        then False
                        else True 
   
                let sidMain :: SID = (show ("maincast", pid, round, w), show (pid, parties, ""))
                writeChan p2f (sidMain, CastP2F_cast (AUX round w))
              
                readChan toMainOK
        
    return () 


testEnvABAHonest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let sid = ("sidTestEnvMulticastCoin", show (["Alice", "Bob", "Charlie", "Mary"], 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty 

    fork $ forever $ do
        --(pid, (s, m)) <- readChan p2z
        (pid, m) <- readChan p2z
        liftIO $ putStrLn $ "Z: party[" ++ pid ++ "] output " ++ show m
        ?pass

    fork $ forever $ do 
        m <- readChan a2z
        liftIO $ putStrLn $ "Z: a sent " ++ show m 
        ?pass

   --let sid1 :: SID = ("sidX", show ("Alice", ["Alice", "Bob", "Charlie", "Mary"], ""))
    () <- readChan pump
    writeChan z2p ("Alice", ClockP2F_Through True)
    
    () <- readChan pump
    writeChan z2p ("Bob", ClockP2F_Through True)

    () <- readChan pump
    writeChan z2p ("Charlie", ClockP2F_Through True)

    () <- readChan pump
    writeChan z2p ("Mary", ClockP2F_Through True)
   
    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks

    -- Deliver Alice's message to herself
    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

    ---- Deliver Bob's message to Alice 
    --() <- readChan pump
    --writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 3)

    -- Deliver Charlie's message to Alice
    --() <- readChan pump
    --writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 6)


testABAHonest = runITMinIO 120 $ execUC testEnvABAHonest (runAsyncP protABA) (runAsyncF $ bangFAsync $ fMulticastAndCoin) dummyAdversary

