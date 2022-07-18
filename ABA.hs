{-
    Open questions regarding the protocol in https://arxiv.org/pdf/2002.08765.pdf:
        1. In the first round if a party is given input Propose(X) then you end up s_broadcasting X. If all other parties s_broadcast ~X instead,
            should you accept them towards a county for the ~X value or ignore it because you've only spawned an instance of s_broadcast for X.
            There is a place in the protocol where in round+1 it will attempt to try ~X to see if it is a valid choice to commit to so maybe it is
            correct to ignore the message. It will be checked in round+1.


    Some Assumptions Made: the protocol seems to assume that all the honest parties must be given
        propose(v) input otherwise you don't get the guarantees of the protocol. 

-}


 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures
  #-} 

module ABA where

import ProcessIO
import StaticCorruptions
import Async
import Multisession

import Safe
import Data.List (findIndex)
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM, liftM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map, (!))
import qualified Data.Map.Strict as Map


forMseq_ xs f = sequence_ $ map f xs

data CastP2F a = CastP2F_cast a | CastP2F_ro Int deriving Show
data CastF2P a = CastF2P_OK | CastF2P_Deliver a | CastF2P_ro Bool deriving (Show, Eq)
data CastF2A a = CastF2A a | CastF2A_ro Bool deriving (Show, Eq)
data CastA2F a = CastA2F_Deliver PID a deriving Show

fMulticastAndCoin :: MonadFunctionalityAsync m t =>
    Functionality (CastP2F t) (CastF2P t) (CastA2F t) (CastF2A t) Void Void m
fMulticastAndCoin (p2f, f2p) (a2f, f2a) (z2f, f2z) = do

    let sid = ?sid :: SID
    let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "fMulticastAndCoin" $ snd sid
    
    let print x = do
            liftIO $ putStrLn $ x

    -- strong coin requires the same coin for each party in a round
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
                        ?leak x
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

data ABACast = AUX Int Bool | EST Int Bool deriving (Show, Eq)

sBroadcast :: (MonadIO m, MonadITM m) => 
    Int -> PID -> [PID] -> Int -> Bool -> Chan (PID, CastF2P ABACast) -> Chan (SID, CastP2F ABACast) -> Chan () -> Chan () -> IORef (Map Bool Bool) -> Bool -> m () -> m ()
sBroadcast tThreshold pid parties round bit f2p p2f okChan toMainChan binptr shouldBCast pass = do
    -- set the current bin_ptr[s_i] = False because main protocol will wait till one of them is True
    modifyIORef binptr $ Map.insert bit False
    vCount <- newIORef 0
    receivedESTFrom <- newIORef $ (Map.empty :: Map PID ())
    receivedAUXFrom <- newIORef $ (Map.empty :: Map PID ())

    -- the SSID for the sub-session of fMulticats this instance of sBroadcast will use      
    let sidmycast :: SID = (show ("sbcast", pid, round, bit), show (pid, parties, ""))

    if shouldBCast then do
        -- broadcast the proposed value
        writeChan p2f (sidmycast, CastP2F_cast (EST round bit))
        readChan okChan 
    else
        return ()

    fork $ forever $ do
        -- assumed we're receiving from the correct session of fMulticast by the dispatcher
        -- in the main protocol body
        (from, m) <- readChan f2p

        case m of
            -- Receiving messages from other parties with TAG,S_VAL(v_i) where TAG is EST[r_i] where r_i is the round this sBroadcast is for
            CastF2P_Deliver (EST r b) -> do
                -- Only consider messages received for the same `bit` and from other parties
                receivedFromPidS <- readIORef receivedESTFrom >>= return . (member from)

                -- Only accept EST messages from new parties
                if (b == bit) && (not receivedFromPidS) then do
                    -- count how many we've received
                    modifyIORef vCount $ (+) 1
                    modifyIORef receivedESTFrom $ Map.insert from ()

                    v <- readIORef vCount
                    liftIO $ putStrLn $ "[" ++ show pid ++ ", " ++ show bit ++ "] vcount: " ++ show v

                    if (v == (tThreshold + 1)) then do
                        -- only broadcast EST round bit if we haven't before
                        if (not shouldBCast) then do
                            writeChan p2f (sidmycast, CastP2F_cast (EST round bit))
                            readChan okChan
                            pass
                        else do
                            pass
                    else if v == ((tThreshold * 2) + 1) then do
                        -- if the second threshold is reached for this bit then set the svalue_i (i.e. the bin_ptr[bit]) to True
                        liftIO $ putStrLn $ "\nsBroadcast [" ++ show pid  ++ ", " ++ show bit ++ ", " ++ show round ++ ", " ++ show shouldBCast ++ "] svalue for " ++ show bit ++ " is True\n"
                        modifyIORef binptr $ Map.insert bit True
                        -- notify the main protocol that this sBroadcast value has been set to True
                        writeChan toMainChan ()  
                    else do
                        pass
                else pass
            _ -> pass 

    -- pass control back to the main protocol body
    writeChan toMainChan ()
        

--data ABAF2P = ABAF2P_Out Bool deriving Show
data ABAF2P = ABAF2P_Out Bool | ABAF2P_Ok deriving (Show, Eq)

protABA :: MonadAsyncP m =>
    Protocol (ClockP2F Bool) ABAF2P (SID, CastF2P ABACast) (SID, CastP2F ABACast) m
protABA (z2p, p2z) (f2p, p2f) = do
    let sid = ?sid :: SID
    let pid = ?pid :: PID
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "fMulticast" $ snd sid 
    let n = length parties

    let ro_sid r = (show ("sRO", r), show("-1", parties, "")) 
    let gprint s r = do
                    liftIO $ putStrLn $ "\ESC[32m [" ++ show pid ++ ", " ++ show r ++ "] " ++ show s ++ "\ESC[0m"

    -- bin_ptrs hold the s_values for each bit, initially both False
    binptr <- newIORef (empty :: Map Bool Bool)
    modifyIORef binptr $ Map.insert False False
    modifyIORef binptr $ Map.insert True False

    -- Separate views that counts unique parties that have sent a TRUE aux message for each round
    viewRTrue <- newIORef (empty :: Map Int Int)
    viewRFalse <- newIORef (empty :: Map Int Int)

    -- read message and route to either sBroadcast or to the main protocol
    f2sbChans <- newIORef (empty :: Map (Int, Bool) (Chan (PID, (CastF2P ABACast))))
    f2sbOKChans <- newIORef (empty :: Map (Int, Bool) (Chan ()))
    sb2mainChans <- newIORef (empty :: Map Int (Chan ()))
    
    viewReady <- newChan
    f2mainOK <- newChan

    -- roundSValue used by the dispatcher to ignore future messages for a round once one of the s_values is already True
    -- TODO: this may be the wrong approach, with a channel that notfied of a True s_value you never have the case that both s_values are True because the channel makes in synchronous in that sense, maybe this is a conquence of UC that we need to discuss 
    roundSValue <- newIORef (empty :: Map Int Bool)
    f2p' <- newChan
    f2p'' <- newChan
    decided <- newIORef False


    -- get the message channel for the SBroadcast instance
    let getSChan s r b d = do
            readIORef f2sbChans >>= return . (! (r, b))

    -- get the OK channel for the SBroadcast instance
    let getOKChan s r b d = do 
            readIORef f2sbOKChans >>= return . (! (r, b))

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
        (s, m) <- readChan f2p'
        isDecided <- readIORef decided
        if not isDecided then do
            let (pidS :: PID, fParties :: [PID], ssid :: String) = readNote "fMulticastAndCoin" $ snd s
            let (sstring :: String, _pidS :: PID, _round :: Int, _bit :: Bool) = readNote "" $ fst s

            -- send to the right sBroadcast or the main protocol body based on ssid
            case m of 
                CastF2P_Deliver (EST r b) -> do
                    -- give the message to the sbcast for this round and bit
                    -- if one of the sbcasts has already set its svalues for TRUE for this round 
                    -- then ignore further messages. TODO: this prohibits the case in the code where
                    -- svalues for both sbcasts is TRUE
                    exists <- readIORef f2sbChans >>= return . (member (r, b))
                    alreadySValues <- readIORef roundSValue >>= return . (! r)
                    if exists && not alreadySValues then do
                        _toS <- getSChan s r b f2sbChans
                        writeChan _toS (pidS, m)
                    else do
                        ?pass 
                CastF2P_Deliver (AUX r b) -> do
                    -- track the view[r_i]
                    if b == True then do
                        modifyIORef viewRTrue $ Map.insertWith (\_ old -> old+1) r 1
                        numTrue <- readIORef viewRTrue >>= return . (! r)
                        liftIO $ putStrLn $ "[" ++ show pid ++ "] num true: " ++ show numTrue
                    else do
                        modifyIORef viewRFalse $ Map.insertWith (\_ old -> old+1) r 1
                        numFalse <- readIORef viewRFalse >>= return . (! r)
                        liftIO $ putStrLn $ "[" ++ show pid ++ "] num false: " ++ show numFalse
                    -- Determine whetherh view[r] is satisified for either of the bits
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
                    -- if some view[r] is satisfied notify the main code block
                    if result then writeChan viewReady (pidS, m) else ?pass
                CastF2P_OK -> do
                    -- Deliver the OK message back from fMulticast when bcasting
                    -- to either the sbcast or the main body
                    if sstring == "sbcast" then do
                        _toOK <- getOKChan s _round _bit f2sbOKChans
                        writeChan _toOK ()
                    else
                        writeChan f2mainOK ()
                _ -> 
                    writeChan viewReady (?pid, m)
        else ?pass
  
    -- Create the channels for the sBroadcast to use
    -- One channel for p2f --> sbcast, one for p2f OK --> sbcast, and sbcast --> main
    let newSBcastChan _round _bit _f2sb _f2sbok _sb2main = do
                _S <- newChan
                _OK <- newChan
                _toMain <- newChan
                modifyIORef _f2sb $ Map.insert (_round, _bit) _S
                modifyIORef _f2sbok $ Map.insert (_round, _bit) _OK

                exists <- readIORef _sb2main >>= return . (member _round)
                if exists then do
                    ch <- readIORef _sb2main >>= return . (! _round)
                    return (_S, _OK, ch)
                else do
                    modifyIORef _sb2main $ Map.insert _round _toMain
                    return (_S,_OK, _toMain)

    -- function to deploy a new instance of sBroadcast with round r and bit b
    let newSBCast r b shouldBroadcast = do
            (f2sb, f2sbok, sb2main) <- newSBcastChan r b f2sbChans f2sbOKChans sb2mainChans
            sBroadcast t pid parties r b f2sb p2f f2sbok sb2main binptr shouldBroadcast ?pass
            -- wait for the sBCast to do spawn and do its thing then return control back to main body
            s2MainChan <- readIORef sb2mainChans >>= return . (! r) 
            readChan s2MainChan
    
    round <- newIORef 0
   
    -- Get a common coin from the random oracle 
    let commonCoinR r = do
        writeChan p2f (ro_sid r, CastP2F_ro r)
        readChan f2p'' -- get OK back from fMulticast
    
    let ssidFromParams r b = (show ("sbcast", ?pid, r, b), show (?pid, parties, ""))

    -- on input propose(v) from Z:
    msg <- readChan z2p
    case msg of
            ClockP2F_Pass -> error "shouldn't be passing anything"
            ClockP2F_Through v -> do
                r <- readIORef round
                s <- return (not v)
                supportCoin <- (return False)
                newSBCast 1 s False 

                fork $ forever $ do
                    isDecided <- readIORef decided
                    if not isDecided then do
                        modifyIORef round $ (+) 1
                        r <- readIORef round

                        -- no s_value in this round yet
                        modifyIORef roundSValue $ Map.insert r False 
                        liftIO $ putStrLn $ "\n[" ++ show pid ++ "] new round " ++ show r ++ "\n"

                        newSBCast r (not s) (not supportCoin)
                        -- TODO ALWAYS CHECK IF IT IS OKAY TO GIVE BOTH SBCASTS THE SAME
                        -- toMain CHANNEL BECAUSE WE MIGHT GET UNWANTED WRITES FROM PREVIOUS
                        -- ROUND'S SBROADCAST WRITING SOMETHING ALL OF A SUDDEN

                        -- wait for one of the processes to write to the main thread
                        -- saying that they set binptr[b] = True
                        writeChan p2z ABAF2P_Ok
                        s2MainChan <- readIORef sb2mainChans >>= return . (! r) 
                        () <- readChan s2MainChan
                        modifyIORef roundSValue $ Map.insert r True

                        -- check which bin_ptr[bit] is True
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
                        readChan f2mainOK
                        ?pass

                        -- wait for view[r]
                        readChan viewReady

                        -- get strong common coin
                        b <- commonCoinR r
                        gprint ("Common coin: " ++ show b) r
                        
                        -- decide?
                        t <- readIORef viewRTrue >>= return . (member r)
                        f <- readIORef viewRFalse >>= return . (member r)
                        supportCoin <- if t && f then do
                                           return True
                                       else if t || f then do 
                                           if t then do
                                               modifyIORef decided $ not
                                               writeChan p2z (ABAF2P_Out True)
                                           else do
                                               writeChan p2z (ABAF2P_Out False)
                                               modifyIORef decided $ not
                                           return True
                                       else do  
                                           return False

                        -- set the binptr values back to False for the next round
                        modifyIORef binptr $ Map.insert True False
                        modifyIORef binptr $ Map.insert False False
                        return ()
                    else do
                        m <- readChan z2p
                        return ()
     
    return () 


testEnvABAHonestAllTrue z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let sid = ("sidTestEnvMulticastCoin", show (["Alice", "Bob", "Charlie", "Mary"], 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty 

    fork $ forever $ do
        --(pid, (s, m)) <- readChan p2z
        (pid, m) <- readChan p2z
        case m of
            ABAF2P_Out b -> liftIO $ putStrLn $ "\ESC[31mParty [" ++ show pid ++ "] decided " ++ show b ++ "\ESC[0m"
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


testEnvABAOneCruptOneRound z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
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
   
    -- Deliver all EST messages
    forMseq_ [0,3,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- Send Bob's EST to Alice and Charlie
    () <- readChan pump
    let bobSID :: SID = (show ("sbcast", "Bob", 1, False), show ("Bob", parties, ""))
    writeChan z2a $ SttCruptZ2A_A2F $ Right $ (bobSID, CastA2F_Deliver "Alice" $ EST 1 False)
    
    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Right $ (bobSID, CastA2F_Deliver "Charlie" $ EST 1 True)

    -- Deliver all EST messages to corrupt Bob
    forMseq_ [0,2,4] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- Send Bob's EST to Mary
    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Right $ (bobSID, CastA2F_Deliver "Mary" $ EST 1 False)

    -- Deliverall EST messages to Charlie
    forMseq_ [0,1,2] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- Deliverall EST messages to Mary
    forMseq_ [0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- We only stop at the honest partys' s_broadcast setting s_value[1/True] = True
    -- this environment offers nothing more elucidating than checking handling of corrupt party.

    () <- readChan pump
    writeChan outp []

testABAOneCruptOneRound = runITMinIO 120 $ execUC testEnvABAOneCruptOneRound (runAsyncP protABA) (runAsyncF $ bangFAsync $ fMulticastAndCoin) dummyAdversary


testEnvABAHonestMultiRound z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let parties = ["Alice", "Bob", "Charlie", "Mary"]
    let sid = ("sidTestEnvMulticastCoin", show (parties, 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty

    fork $ forever $ do
        --(pid, (s, m)) <- readChan p2z
        (pid, m) <- readChan p2z
        liftIO $ putStrLn $ "\ESC[33m Z: party[" ++ pid ++ "] output " ++ show m ++ "\ESC[0m"
        ?pass

    fork $ forever $ do 
        m <- readChan a2z
        case m of
            SttCruptA2Z_F2A (Left ClockF2A_Pass) -> return ()
            _ -> liftIO $ putStrLn $ "Z: a sent " ++ show m 
        ?pass

    -- tl;dr give half parties True as Input and the other half False and let them reach a consenus on the bit
    () <- readChan pump
    writeChan z2p ("Alice", ClockP2F_Through True)
    
    () <- readChan pump
    writeChan z2p ("Bob", ClockP2F_Through True)

    () <- readChan pump
    writeChan z2p ("Charlie", ClockP2F_Through False)

    () <- readChan pump
    writeChan z2p ("Mary", ClockP2F_Through False)
    () <- readChan pump

    liftIO $ putStrLn $ "\n\ESC[31m Alice and Bob should rebroadcast False\ESC[0m\n"
    -- Deliver ESTs False from Charlie and Mary first
    forMseq_ [0..7] $ \x -> do
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 8)
        () <- readChan pump
        return ()


    liftIO $ putStrLn $ "\n\ESC[31m Mary and Charlie should rebroadcast True\ESC[0m\n"
    -- Deliver the ESTs from Alice and Bob
    forMseq_ [0..7] $ \x -> do
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
        () <- readChan pump
        return ()


    liftIO $ putStrLn $ "\n\ESC[31m Everyone's s_value for False should be set to True\ESC[0m\n"
    -- Deliver Alice and Bob's rebroadcasted Falses
    forMseq_ [0..7] $ \x -> do
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
        () <- readChan pump
        return ()

    liftIO $ putStrLn $ "\n\ESC[31m nothing should happen because they have all already accepted False\ESC[0m\n"
    -- Deliver Charlie and Mary's rebroadcasted Trues (SHOULD DO NOTHING)
    forMseq_ [0..7] $ \x -> do
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
        () <- readChan pump
        return ()
  
    liftIO $ putStrLn $ "\n\ESC[31m Everone gets 3 AUX messages and does something \ESC[0m\n"  
    -- Deliver 3 AUX messages to everyone 
    forMseq_ [0..13] $ \x -> do
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
        () <- readChan pump
        return ()

    --() <- readChan pump
    writeChan outp []
testABAHonestMultiRound = runITMinIO 120 $ execUC testEnvABAHonestMultiRound (runAsyncP protABA) (runAsyncF $ bangFAsync $ fMulticastAndCoin) dummyAdversary
 
testEnvABAMinority z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let parties = ["Alice", "Bob", "Charlie", "Mary", "Teresa"]
    let sid = ("sidTestEnvMulticastCoin", show (parties, 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty

    fork $ forever $ do
        --(pid, (s, m)) <- readChan p2z
        (pid, m) <- readChan p2z
        liftIO $ putStrLn $ "\ESC[33m Z: party[" ++ pid ++ "] output " ++ show m ++ "\ESC[0m"
        ?pass

    fork $ forever $ do 
        m <- readChan a2z
        case m of
            SttCruptA2Z_F2A (Left ClockF2A_Pass) -> return ()
            _ -> liftIO $ putStrLn $ "Z: a sent " ++ show m 
        ?pass

    -- tl;dr give half parties True as Input and the other half False and let them reach a consenus on the bit
    () <- readChan pump
    writeChan z2p ("Alice", ClockP2F_Through True)
    
    () <- readChan pump
    writeChan z2p ("Bob", ClockP2F_Through True)

    () <- readChan pump
    writeChan z2p ("Charlie", ClockP2F_Through True)

    () <- readChan pump
    writeChan z2p ("Mary", ClockP2F_Through False)

    () <- readChan pump
    writeChan z2p ("Teresa", ClockP2F_Through False)

    -- Deliver ESTs False from Charlie and Mary first
    forMseq_ [0..9] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 15)


    -- Deliver ESTs rebroadcast False from Alice 
    forMseq_ [0..4] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 15)

    forMseq_ [0..19] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 35)

    -- TODO: finish but i'm convinced that you can decide on the minority proposal

testABAMinority = runITMinIO 120 $ execUC testEnvABAMinority (runAsyncP protABA) (runAsyncF $ bangFAsync $ fMulticastAndCoin) dummyAdversary
 

data ABAA2F = ABAA2F_Decide Bool | ABAA2F_Input PID Bool deriving Show
data ABAF2A = ABAF2A_Ok deriving Show

-- fABA should leak the inputs of each of the parties, the simulator needs to guarantee BBC-validity where if every party proposes the same value, they all agree on that value 
fABA :: MonadFunctionalityAsync m (PID, Bool) =>
    Functionality Bool ABAF2P ABAA2F ABAF2A Void Void m 
fABA (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
    let sid = ?sid :: SID
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "fABA" $ snd sid

    inputs <- newIORef (empty :: Map PID Bool)
    decision <- newIORef False

    let countInputs = do
                    numTrue <- readIORef inputs >>= return . sum . map (\x -> if x then 1 else 0) . Map.elems
                    numFalse <- readIORef inputs >>= return . sum . map (\x -> if not x then 1 else 0) . Map.elems
                    return (numTrue, numFalse)
    let isAdvChoice = do
        countInputs >>= (\(nt, nf) -> return (((nt > t) && (nf > t)), nt, nf))

    -- party inputs and schedule decision when inputs from honest parties
    fork $ forever $ do
        (pid, m :: Bool) <- readChan p2f
        exists <- readIORef inputs >>= return . (member pid)
        if not exists then do
            modifyIORef inputs $ Map.insert pid m
            ?leak (pid, m)
            
            ready <- readIORef inputs >>= return . ((length parties) ==) . length . Map.keys
            if ready then do
                b <- ?getBit
                isAdvChoice >>= \(u, nt, nf) ->
                       writeIORef decision $ if u then b else if (nt > t) then True else False

                forMseq_ parties $ \pidX -> do
                    eventually $ (readIORef decision >>= \d -> writeChan f2p (pidX, ABAF2P_Out d))
                return ()
            else return ()
            writeChan f2p (pid, ABAF2P_Ok)
            -- ?pass
        else error ("second input for same party " ++ show pid)
    
    -- adversary can set crupt inputs and decide bit
    fork $ forever $ do
        m <- readChan a2f
        case m of 
            -- adv can override any crupt party's input
            ABAA2F_Input p b -> do
                if not $ member p ?crupt then modifyIORef inputs $ Map.insert p b else return ()
            -- if adv choice is set then adv chooses bit
            ABAA2F_Decide b -> 
                isAdvChoice >>= \(c,_,_) -> if c then writeIORef decision b else return ()
        writeChan f2a ABAF2A_Ok
        -- ?pass
    return ()

--- TODO: if there are n=5 parties. 3 of them propose 0 and 2 of the propose 1: is it still possible for them to decide on 0 given the right ordering of delivering the messages? It seems to me that it's a tossup only when there are equal numbers of people proposing 0 and 1. Then the delivery order matters.

testEnvfABAHonest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let parties = ["Alice", "Bob", "Charlie", "Mary"]
    let sid = ("sidfABA", show (parties, 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty 

    fork $ forever $ do
        --(pid, (s, m)) <- readChan p2z
        (pid, m) <- readChan p2z
        case m of
            ABAF2P_Out b -> liftIO $ putStrLn $ "\ESC[31mParty [" ++ show pid ++ "] decided " ++ show b ++ "\ESC[0m"
            _ -> printEnvReal "OK"
        ?pass

    fork $ forever $ do 
        m <- readChan a2z
        liftIO $ putStrLn $ "Z: a sent " ++ show m 
        ?pass

    () <- readChan pump
    writeChan z2p ("Alice", ClockP2F_Through True)
    () <- readChan pump
    writeChan z2p ("Bob", ClockP2F_Through True)
    () <- readChan pump
    writeChan z2p ("Charlie", ClockP2F_Through False)
    () <- readChan pump
    writeChan z2p ("Mary", ClockP2F_Through False)

    -- Adversary should be able to set the bit now
    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F (Right (ABAA2F_Decide True))

    forMseq_ [0..3] $ \_ -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
     
testfABAHonest= runITMinIO 120 $ execUC testEnvfABAHonest idealProtocol (runAsyncF $ fABA) dummyAdversary


makeSyncLog handler req = do
  ctr <- newIORef 0
  let syncLog = do
        -- Post the request
        log <- req
        -- Only process the new elements
        t <- readIORef ctr
        let tail = drop t log
        modifyIORef ctr (+ length tail)
        forM tail handler
        return ()
  return syncLog

simABA :: MonadAdversary m => Adversary (SttCruptZ2A (ClockP2F (SID, CastP2F ABACast))
                                            (Either ClockA2F (SID, CastA2F ABACast)))
                                        (SttCruptA2Z (SID, CastF2P ABACast)
                                            (Either (ClockF2A (SID, ABACast))
                                                    (SID , CastF2A ABACast)))
                                        ABAF2P (ClockP2F Bool)
                                        (Either (ClockF2A (PID, Bool)) ABAF2A) (Either ClockA2F ABAA2F) m
simABA (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
    let sid :: SID = ?sid
    let (parties :: [PID], t :: Int, sssid :: String) = readNote "ABA" $ snd sid

    numTrue <- newIORef 0
    numFalse <- newIORef 0
    partiesToDeliver <- newIORef parties

    -- routing z2a <-->
    sbxpump <- newChan
    sbxz2p <- newChan
    sbxp2z <- newChan

    let sbxEnv z2exec (p2z', z2p') (a2z', z2a') _ pump' outp' = do
        writeChan z2exec $ SttCrupt_SidCrupt ?sid ?crupt

        forward p2z' sbxp2z
        forward sbxz2p z2p'

        forward z2a z2a'
        forward a2z' a2z

        forward pump' sbxpump
    
        return ()

    let sbxBullRand () = bangFAsync fMulticastAndCoin
   
    -- monitor the sandbox for outputs  
    chanOk <- newChan
    
    fork $ forever $ do
        mf <- readChan sbxp2z
        case mf of
            (_pidS, ABAF2P_Ok) -> writeChan chanOk ()
            (_pidS, ABAF2P_Out b) -> do
                -- simulator just tries to force the bit: give all crupt
                -- parties b as input and try to force the decision
                forMseq_ (Map.keys ?crupt) $ \pidC -> do
                    writeChan a2p (pidC, ClockP2F_Through b)
                    readChan p2a  --OK messsage

                -- also try to set the bit in fABA just in case
                writeChan a2f (Right (ABAA2F_Decide b))
                readChan f2a --OK
    
                -- Deliver this pid's output in fABA
                idx <- readIORef partiesToDeliver >>= return . (findIndex (== _pidS))
                case idx of
                    Just x -> do 
                        modifyIORef partiesToDeliver (deleteNth x)
                        writeChan a2f (Left (ClockA2F_Deliver x))
                    _ -> error "pid that doens't exist"
    
    let handleLeak m = do
        printAdv $ "handleLeak simulator"
        let (pid, b) = m
        case b of
            True -> modifyIORef numTrue (+ 1)
            False -> modifyIORef numFalse (+ 1)
        writeChan sbxz2p (pid, ClockP2F_Through b)
        () <- readChan chanOk
        --() <- readChan sbxpump
        return ()

    syncLeaks <- makeSyncLog handleLeak $ do
        writeChan a2f $ Left ClockA2F_GetLeaks
        mf <- readChan f2a
        let Left (ClockF2A_Leaks leaks) = mf
        return leaks

    let sbxProt () = protABA

    let sbxAdv (z2a',a2z') (p2a',a2p') (f2a',a2f') = do
        fork $ forever $ do
            mf <- readChan z2a'
            printAdv $ show "Intercepted z2a'" ++ show mf
            syncLeaks
            printAdv $ "forwarding into the sandbox"
            case mf of
                SttCruptZ2A_A2F f -> writeChan a2f' f
                SttCruptZ2A_A2P pm -> writeChan a2p' pm
        fork $ forever $ do
            m <- readChan f2a'
            liftIO $ putStrLn $ show "f2a'" ++ show m
            writeChan a2z' $ SttCruptA2Z_F2A m
        fork $ forever $ do
            (pid,m) <- readChan p2a'
            liftIO $ putStrLn $ "p2a'"
            writeChan a2z' $ SttCruptA2Z_P2A (pid, m)
        return ()

    mf <- selectRead z2a f2a

    fork $ execUC_ sbxEnv (runAsyncP $ sbxProt ()) (runAsyncF (sbxBullRand ())) sbxAdv
    () <- readChan sbxpump

    case mf of
        Left m -> writeChan z2a m
        Right m -> writeChan f2a m

    fork $ forever $ do
        () <- readChan sbxpump
        undefined
        return ()

    return ()

testEnvSimHonest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let sid = ("sidTestEnvMulticastCoin", show (["Alice", "Bob", "Charlie", "Mary"], 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid empty 

    transcript <- newIORef []
    
    fork $ forever $ do
        --(pid, (s, m)) <- readChan p2z
        (pid, m) <- readChan p2z
        modifyIORef transcript (++ [Right (pid, m)])
        case m of
            ABAF2P_Out b -> liftIO $ putStrLn $ "\ESC[33mParty [" ++ show pid ++ "] decided " ++ show b ++ "\ESC[0m"
            _ -> printEnvReal "OK"
        ?pass

    fork $ forever $ do 
        m <- readChan a2z
        modifyIORef transcript (++ [Left m])
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

    () <- readChan pump
    writeChan outp =<< readIORef transcript
 
testSimHonest = runITMinIO 120 $ execUC testEnvSimHonest idealProtocol (runAsyncF $ fABA) simABA

testCompare :: IO Bool
testCompare = runITMinIO 120 $ do
    liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
    t1 <- execUC
            testEnvSimHonest
            (runAsyncP protABA)
            (runAsyncF $ bangFAsync fMulticastAndCoin)
            dummyAdversary
    liftIO $ putStrLn ""
    liftIO $ putStrLn ""
    liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
    t2 <- execUC
            testEnvSimHonest
            idealProtocol
            (runAsyncF $ fABA)
            simABA
    return (t1 == t2)


testEnvSimCrupt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let parties = ["Alice", "Bob", "Charlie", "Mary"]
    let sid = ("sidTestEnvMulticastCoin", show (parties, 1, ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Bob",())]

    transcript <- newIORef []
    
    fork $ forever $ do
        --(pid, (s, m)) <- readChan p2z
        (pid, m) <- readChan p2z
        modifyIORef transcript (++ [Right (pid, m)])
        case m of
            ABAF2P_Out b -> liftIO $ putStrLn $ "\ESC[33mParty [" ++ show pid ++ "] decided " ++ show b ++ "\ESC[0m"
            _ -> printEnvReal "OK"
        ?pass

    fork $ forever $ do 
        m <- readChan a2z
        modifyIORef transcript (++ [Left m])
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
   
    -- Deliver all EST messages
    forMseq_ [0,3,6] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- Send Bob's EST to Alice and Charlie
    () <- readChan pump
    let bobSID :: SID = (show ("sbcast", "Bob", 1, False), show ("Bob", parties, ""))
    writeChan z2a $ SttCruptZ2A_A2F $ Right $ (bobSID, CastA2F_Deliver "Alice" $ EST 1 False)
    
    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Right $ (bobSID, CastA2F_Deliver "Charlie" $ EST 1 True)

    -- Deliver all EST messages to corrupt Bob
    forMseq_ [0,2,4] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- Send Bob's EST to Mary
    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Right $ (bobSID, CastA2F_Deliver "Mary" $ EST 1 False)

    -- Deliverall EST messages to Charlie
    forMseq_ [0,1,2] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- Deliverall EST messages to Mary
    forMseq_ [0,0,0] $ \x -> do
        () <- readChan pump
        writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver x)

    -- We only stop at the honest partys' s_broadcast setting s_value[1/True] = True
    -- this environment offers nothing more elucidating than checking handling of corrupt party.

    () <- readChan pump
    writeChan outp =<< readIORef transcript

testCruptCompare :: IO Bool
testCruptCompare = runITMinIO 120 $ do
    liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
    t1 <- execUC
            testEnvSimCrupt
            (runAsyncP protABA)
            (runAsyncF $ bangFAsync fMulticastAndCoin)
            dummyAdversary
    liftIO $ putStrLn ""
    liftIO $ putStrLn ""
    liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
    t2 <- execUC
            testEnvSimCrupt
            idealProtocol
            (runAsyncF $ fABA)
            simABA

    liftIO $ putStrLn "REAL WORLD"
    liftIO $ putStrLn (show t1)
    liftIO $ putStrLn ""
    liftIO $ putStrLn ""
    liftIO $ putStrLn "IDEAL WORLD"
    liftIO $ putStrLn (show t2)


    return (t1 == t2)
