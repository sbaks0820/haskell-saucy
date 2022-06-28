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
                            --liftIO $ putStrLn $ "adding eventually for receiver [" ++ show pidR ++ "]"
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
    -- set the current bin_ptr[s_i] = False because main protocol will wait till one of them is True
    liftIO $ putStrLn $ "\nsBroadcast [" ++ show pid ++ "] bit [" ++ show bit ++ "] shouldBroadcast [" ++ show shouldBCast ++ "] round [" ++ show round ++ "]\n"
    modifyIORef binptr $ Map.insert bit False
    vCount <- newIORef 0
    receivedESTFrom <- newIORef $ (Map.empty :: Map PID ())
    receivedAUXFrom <- newIORef $ (Map.empty :: Map PID ())

    let firstThreshold = False
    let secondThreshold = True
    
    -- the SSID for the sub-session of fMulticats this instance of sBroadcast will use      
    let sidmycast :: SID = (show ("sbcast", pid, round, bit), show (pid, parties, ""))

    if shouldBCast then do
        -- broadcast according to paper specification
        writeChan p2f (sidmycast, CastP2F_cast (EST round bit))
        readChan okChan 
        -- TODO? 
        -- require (pidS == pid) "OK from wrong fMulticast session"
        --pass
    else 
        return ()

    fork $ forever $ do
        -- assumed we're receiving from the correct session of fMulticast by the dispatcher
        -- in the main protocol body
        (from, m) <- readChan f2p
        liftIO $ putStrLn $ "\nGot something at sBCast [" ++ show pid  ++ ", " ++ show bit ++ ", " ++ show round ++ ", " ++ show shouldBCast++ "] msg " ++ show m 

        case m of
            -- Receiving messages from other parties with TAG,S_VAL(v_i) where TAG
            -- is EST[r_i] where r_i is the round this sBroadcast is for
            CastF2P_Deliver (EST r b) -> do
                -- Only consider messages received for the same `bit` and from other parties
                liftIO $ putStrLn $ "[EST " ++ show pid ++ "] received EST message from [" ++ show from ++ "]"
                receivedFromPidS <- readIORef receivedESTFrom >>= return . (member from)
                if (b == bit) && (not receivedFromPidS) then do
                    --liftIO $ putStrLn $ ("sBroadcast [" ++ show pid ++ ", " ++ show bit ++ ", " ++ show round ++ ", " ++ show shouldBCast ++ "] got someone elses message for the same bit [" ++ show b ++ "]")
                    -- count how many we've received
                    modifyIORef vCount $ (+) 1
                    modifyIORef receivedESTFrom $ Map.insert from ()
                    _v <- readIORef vCount
                    liftIO $ putStrLn $ "[" ++ show pid ++ "] vcount: " ++ show _v
                    if (_v == (tThreshold + 1)) then do
                        -- only broadcast EST round bit if we haven't before
                        if (not shouldBCast) then do
                            liftIO $ putStrLn $ ("sBroadcast [" ++ show pid  ++ ", " ++ show bit ++ ", " ++ show round ++ ", " ++ show shouldBCast++ "] broadcasting EST " ++ show round ++ " " ++ show bit)
                            writeChan p2f (sidmycast, CastP2F_cast (EST round bit))
                            readChan okChan
                        else do
                            --liftIO $ putStrLn $ "Met threshold but nothing to do"
                            --return ()
                            pass
                    else if _v == ((tThreshold * 2) + 1) then do
                        -- if the second threshold is reached for this bit then set the 
                        -- svalue_i (i.e. the bin_ptr[bit]) to True
                        liftIO $ putStrLn $ "\n****** sBroadcast [" ++ show pid  ++ ", " ++ show bit ++ ", " ++ show round ++ ", " ++ show shouldBCast ++ "] met second threshold, svalue is now True\n"
                        modifyIORef binptr $ Map.insert bit True
                        -- notify the main protocol that this sBroadcast value has been set to True
                        writeChan toMainChan ()
                    else do
						error "Received neither an AUX message or an EST messate tf"
                else pass
            _ -> pass 

    -- pass control back to the main protocol body
    writeChan toMainChan ()
    --return ()
        

data ABAF2P = ABAF2P_Out Bool deriving Show

protABA :: MonadAsyncP m =>
    Protocol (ClockP2F Bool) ABAF2P (SID, CastF2P ABACast) (SID, CastP2F ABACast) m
protABA (z2p, p2z) (f2p, p2f) = do
    let sid = ?sid :: SID
    let pid = ?pid :: PID
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "fMulticast" $ snd sid 
    let n = length parties

    view <- newIORef (empty :: Map Int [Bool])
    binptr <- newIORef (empty :: Map Bool Bool)
    modifyIORef binptr $ Map.insert False False
    modifyIORef binptr $ Map.insert True False

    viewRTrue <- newIORef (empty :: Map Int Int)
    viewRFalse <- newIORef (empty :: Map Int Int)

    -- read message and route to either sBroadcast or to the main protocol
    -- manyS <- newIORef (empty :: Map Int (Chan (PID, (CastF2P ABACast))))
    --manyS <- newIORef (empty :: Map (SID, Int, Bool) (Chan (PID, (CastF2P ABACast))))
    --manyOK <- newIORef (empty :: Map (SID, Int, Bool) (Chan ()))
    manyS <- newIORef (empty :: Map (Int, Bool) (Chan (PID, (CastF2P ABACast))))
    manyOK <- newIORef (empty :: Map (Int, Bool) (Chan ()))
    manyStoMain <- newIORef (empty :: Map Int (Chan ()))
    toMain <- newChan
    toMainOK <- newChan
    roRespond <- newChan
    f2p' <- newChan
    f2p'' <- newChan
    decided <- newIORef False


    -- create 2 channels for SBroadcast, one for messages
    -- and one for OK from fMulticast
    let newSBcastChan s r b ms mok m2m = do
                _S <- newChan
                _OK <- newChan
                _toMain <- newChan
                --modifyIORef ms $ Map.insert (s, r, b) _S
                --modifyIORef mok $ Map.insert (s, r, b) _OK
                modifyIORef ms $ Map.insert (r, b) _S
                modifyIORef mok $ Map.insert (r, b) _OK

                exists <- readIORef m2m >>= return . (member r)
                if exists then do
                    ch <- readIORef m2m >>= return . (! r)
                    return (_S, _OK, ch)
                else do
                    modifyIORef m2m $ Map.insert r _toMain
                    return (_S,_OK, _toMain)

    -- get the message channel for the SBroadcast instance
    let getSChan s r b d = do
            readIORef manyS >>= return . (! (r, b))
            --readIORef manyS >>= return . (! (s, r, b))

    -- get the OK channel for the SBroadcast instance
    let getOKChan s r b d = do 
            readIORef manyOK >>= return . (! (r, b))
            --readIORef manyOK >>= return . (! (s, r, b))

    -- Compute the ssid from the broadcast parameters
    -- Identify messages by sid, round, and bit of SBroadcast
    let ssidFromParams r b = (show ("sbcast", ?pid, r, b), show (?pid, parties, ""))

    fork $ forever $ do
        (s, m) <- readChan f2p
        let (pidS :: PID, fParties :: [PID], ssid :: String) = readNote "fMulticastAndCoin" $ snd s

        case m of 
            CastF2P_ro b -> do
                writeChan f2p'' b
            _ -> do
                writeChan f2p' (s, m)

    -- dispatcher from F to sBroadcast and main protocol body  
    -- and dispatcher between sBroadcast and main protocol body
    fork $ forever $ do
        isDecided <- readIORef decided
        if not isDecided then do
            (s, m) <- readChan f2p'
            let (pidS :: PID, fParties :: [PID], ssid :: String) = readNote "fMulticastAndCoin" $ snd s
            let (sstring :: String, _pidS :: PID, _round :: Int, _bit :: Bool) = readNote "" $ fst s

            -- index channels by the SSID and send to the appropriate instance of either sBroadcast
            -- or the main protocol body
            case m of 
                CastF2P_Deliver (EST r b) -> do
                    liftIO $ putStrLn $ "[" ++ show pid ++ "] receives EST from " ++ show pidS
                    exists <- readIORef manyS >>= return . (member (r, b))
                    _toS <- getSChan s r b manyS
                    writeChan _toS (pidS, m)
                CastF2P_Deliver (AUX r b) -> do
                    --writeChan toMain (pidS, m)
                    -- track the view[r_i]
                    liftIO $ putStrLn $ "\n[" ++ show pid ++ "] AUX message (" ++ show r ++ ", " ++ show b ++ ") from " ++ show pidS ++ show "\n"
                    if pidS /= pid then do
                        if b == True then do
                            modifyIORef viewRTrue $ Map.insertWith (\_ old -> old+1) r 1
                            numTrue <- readIORef viewRTrue >>= return . (! r)
                            liftIO $ putStrLn $ "num true: " ++ show numTrue
                        else do
                            modifyIORef viewRFalse $ Map.insertWith (\_ old -> old+1) r 1
                            numFalse <- readIORef viewRTrue >>= return . (! r)
                            liftIO $ putStrLn $ "num false: " ++ show numFalse
                        isTrue <- readIORef viewRTrue >>= return . (member r) 
                        isFalse <- readIORef viewRFalse >>= return . (member r)
                        result <- if isTrue && isFalse then do
                                      tN <- readIORef viewRTrue >>= return . (! r)
                                      fN <- readIORef viewRFalse >>= return . (! r)
                                      if tN == (n-t) && fN == (n-t) then return True else return False
                                  else if isTrue then do 
                                      tN <- readIORef viewRTrue >>= return . (! r)
                                      if tN == (n-t) then return True else return False
                                  else do
                                      fN <- readIORef viewRFalse >>= return . (! r)
                                      if fN == (n-t) then return True else return False
                        if result then writeChan toMain (pidS, m) else ?pass
                    else ?pass
                    --_toS <- getSChan s r b manyS
                CastF2P_OK -> do
                    if sstring == "sbcast" then do
                        _toOK <- getOKChan s _round _bit manyOK
                        writeChan _toOK ()
                    else
                        writeChan toMainOK ()
                _ -> 
                    writeChan toMain (?pid, m)
        else return ()
  
    -- function to deploy a new instance of sBroadcast with  
    let newSBCast r v shouldBroadcast = do
            (sf2p, sok, stomain) <- newSBcastChan (ssidFromParams r v) r v manyS manyOK manyStoMain
            sBroadcast t pid parties r v sf2p p2f sok stomain binptr shouldBroadcast ?pass

    round <- newIORef 0
    
    let commonCoinR r = do
        let sidRO :: SID = (show ("sRO", r), show (?pid, parties, ""))
        writeChan p2f (sidRO, CastP2F_ro r)
        readChan f2p''
    
    let ssidFromParams r b = (show ("sbcast", ?pid, r, b), show (?pid, parties, ""))

    -- on input propose(v) from Z:
    msg <- readChan z2p
    case msg of
            ClockP2F_Pass -> error "shouldn't be passing anything"
            ClockP2F_Through v -> do
                r <- readIORef round
                s <- return (not v)
                supportCoin <- (return False)
                newSBCast r s False 
                -- wait for the sBCast to do it's thing
                s2MainChan <- readIORef manyStoMain >>= return . (! r) 
                readChan s2MainChan

                fork $ forever $ do
                    isDecided <- readIORef decided
                    if not isDecided then do
                        modifyIORef round $ (+) 1
                        r <- readIORef round
                        liftIO $ putStrLn $ "\n[" ++ show pid ++ "] new round " ++ show r ++ "\n"

                        --m <- readChan z2p
                        newSBCast r (not s) (not supportCoin)
                        -- TODO ALWAYS CHECK IF IT IS OKAY TO GIVE BOTH SBCASTS THE SAME
                        -- toMain CHANNEL BECAUSE WE MIGHT GET UNWANTED WRITES FROM PREVIOUS
                        -- ROUND'S SBROADCAST WRITING SOMETHING ALL OF A SUDDEN
                        s2MainChan <- readIORef manyStoMain >>= return . (! r) 
                        readChan s2MainChan

                        -- wait for one of the processes to write to the main thread
                        -- saying that they set binptr[b] = True
                        --liftIO $ putStrLn $ "Waiting for an sBroadcast to return True"
                        ?pass 
                        () <- readChan s2MainChan
                        liftIO $ putStrLn $ "[" ++ show pid ++ "] sValue is True for one of the SBCasts"

                        -- check which bit bin_ptr is True
                        b0 <- readIORef binptr >>= return . (! False)
                        b1 <- readIORef binptr >>= return . (! True)

                        -- set w for broadcast
                        let w = if supportCoin
                                then s
                                else if b0
                                then False
                                else True 
   
                        let sidMain :: SID = (show ("maincast", pid, r, w), show (pid, parties, ""))
                        writeChan p2f (sidMain, CastP2F_cast (AUX r w))
                        readChan toMainOK
                        ?pass

                        -- wait for view[r]
                        readChan toMain

                        -- get strong common coin
                        b <- commonCoinR r
                        liftIO $ putStrLn $ "[" ++ show pid ++ "] Common coin: " ++ show b
                        
                        -- decide?
                        t <- readIORef viewRTrue >>= return . (member r)
                        f <- readIORef viewRFalse >>= return . (member r)
                        supportCoin <- if t && f then return True
                                       else if t || f then do 
                                           if t then do
                                               modifyIORef decided $ not
                                               writeChan p2z (ABAF2P_Out True)
                                           else do
                                               writeChan p2z (ABAF2P_Out False)
                                               modifyIORef decided $ not
                                           return True
                                       else return False
                        return ()
                    else return ()
     
    return () 


testEnvABAHonestAllTrue z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
   
    -- Deliver all EST messages to Alice
    forMseq_ [0,3,6,9] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
    
    -- Deliver all EST messages to Bob
    forMseq_ [0,2,4,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- Deliver all EST messages to Charlie
    forMseq_ [0,1,2,3] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
    
    -- Deliver all EST messages to Mary
    forMseq_ [0,0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- Deliver all AUX messages to Alice 
    forMseq_ [0,3,6,9] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
    
    -- Deliver all AUX messages to Bob
    forMseq_ [0,2,4,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- Deliver all AUX messages to Charlie
    forMseq_ [0,1,2,3] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)
    
    -- Deliver all AUX messages to Mary
    forMseq_ [0,0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

testABAHonestAllTrue = runITMinIO 120 $ execUC testEnvABAHonestAllTrue (runAsyncP protABA) (runAsyncF $ bangFAsync $ fMulticastAndCoin) dummyAdversary


testEnvABAHonest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let parties = ["Alice", "Bob", "Charlie", "Mary"]
    let sid = ("sidTestEnvMulticastCoin", show (parties, 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Bob",())]

    fork $ forever $ do
        --(pid, (s, m)) <- readChan p2z
        (pid, m) <- readChan p2z
        liftIO $ putStrLn $ "Z: party[" ++ pid ++ "] output " ++ show m
        ?pass

    fork $ forever $ do 
        m <- readChan a2z
        liftIO $ putStrLn $ "Z: a sent " ++ show m 
        ?pass

    () <- readChan pump
    writeChan z2p ("Alice", ClockP2F_Through True)
    
    --() <- readChan pump
    --writeChan z2p ("Bob", ClockP2F_Through True)

    () <- readChan pump
    writeChan z2p ("Charlie", ClockP2F_Through True)

    () <- readChan pump
    writeChan z2p ("Mary", ClockP2F_Through True)
   
    -- Deliver all EST messages to Alice
    forMseq_ [0,3,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

	let bobSID :: SID = (show ("sbcast", "Bob", 1, False), show ("Bob", parties, ""))
	writeChan z2a $ SttCruptZ2A_A2F $ Right $ (bobSID, CastA2F_Deliver "Alice" $ EST 1 False)
    

testABAHonest = runITMinIO 120 $ execUC testEnvABAHonest (runAsyncP protABA) (runAsyncF $ bangFAsync $ fMulticastAndCoin) dummyAdversary
