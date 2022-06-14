{-# LANGUAGE ScopedTypeVariables, ImplicitParams #-}
{-# LANGUAGE PartialTypeSignatures, RankNTypes #-}

module StateChannel where

import ProcessIO
import StaticCorruptions
import Multisession
import Async
import Contracts

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map, (!))
import qualified Data.Map.Strict as Map

forMseq_ xs f = sequence_ $ map f xs

data StateP2F a = StateP2F_Input a deriving Show
data StateF2P a = StateF2P_State a deriving Show

type UpdateFunction st inp auxin auxout = st -> inp -> auxin -> (auxout, st)
type PayState = (Int, [Int], Int, [Int]) 
type AuxOutput = (Int, Int)
type AuxInput = (Int, Int)
type PayInput = ([Int], Int)

data CPayP2F = CPayP2F_Deposit Int | CPayP2F_GetDeposit deriving Show
data CPayF2P = CPayF2P_Deposit (Int, Int) deriving Show
data CPayF2C = CPayF2C_Output AuxOutput deriving Show
data CPayC2F = CPayC2F_AuxIn AuxInput deriving Show



uPayPayments :: [Int] -> Int -> Int -> Int -> [Int]
uPayPayments [] wd bound curr = []
uPayPayments (x:xs) wd bound curr = if (x + curr) <= bound then 
                                        [x] ++ uPayPayments xs wd bound (curr + x)
                                    else
                                        uPayPayments xs wd bound curr

procParty pid d c inputs =
    case (inputs ! pid) of
            Nothing -> do
                let n = uPayPayments [] 0 (d+c) 0
                (n, sum n, 0)
            Just (arr, wd) -> do
                let n :: [Int] = uPayPayments arr wd (d + c) 0
                if wd >= (d + c - (sum n)) then (n, sum n, 0)
                else (n, sum n, wd)
    

    
uPay :: UpdateFunction PayState (Map PID (Maybe PayInput)) CPayC2F CPayF2C
uPay state inputs auxin = do
    let (credL :: Int, oldarrL :: [Int], credR :: Int, oldarrR :: [Int]) = state
    let CPayC2F_AuxIn (depositsL :: Int, depositsR :: Int) = auxin

    let processParty pid d c = case (inputs ! pid) of
                                       Nothing -> do
                                           let n = uPayPayments [] 0 (d+c) 0
                                           (n, sum n, 0)
                                       Just (arr, wd) -> do
                                           let n :: [Int] = uPayPayments arr wd (d + c) 0
                                           if wd >= (d + c - (sum n)) then (n, sum n, 0)
                                           else (n, sum n, wd)
  
    
    -- process left
    let (newArrL, payL, wdL) = processParty "Alice" depositsL credL

    -- process right
    let (newArrR, payR, wdR) = processParty "Bob" depositsR credR
    
    let realCredL = credL + payR - payL - wdL
    let realCredR = credR + payL - payR - wdR

    let auxOut = if (wdL /= 0) || (wdR /= 0) then (wdL, wdR)
                 else (0,0)  

    (CPayF2C_Output auxOut, (realCredL, newArrL, realCredR, newArrR))

main :: IO ()
main = do
    liftIO $ putStrLn $ "output on ([], 1), ([], 1): " ++ show (uPay (0, [], 0, []) (Map.fromList [("Alice", Just ([], 1)), ("Bob", Just ([], 1))]) (CPayC2F_AuxIn (10,10)))

    liftIO $ putStrLn $ "output of processPay: " ++ show (procParty "Alice" 10 0 (Map.fromList [("Alice", Just ([], 1))]))
    return ()


contractPay :: MonadContract m => Contract CPayP2F CPayF2P CPayF2C CPayC2F () m
contractPay (p2f, f2p) (f2c, c2f) emit = do
    depositsL <- newIORef 0
    depositsR <- newIORef 0

    fork $ forever $ do
        --(pid, CPayDeposit x) <- readChan p2f
        (pid, m) <- readChan p2f
        case m of
            CPayP2F_Deposit x -> do
                if pid == "Alice" then do
                    modifyIORef depositsL $ (+) x
                else if pid == "Bob" then do
                    modifyIORef depositsR $ (+) x
                else error "who is this person?"
                dl <- readIORef depositsL
                dr <- readIORef depositsR
                writeChan c2f (CPayC2F_AuxIn (dl, dr))
            CPayP2F_GetDeposit -> do
                dl <- readIORef depositsL
                dr <- readIORef depositsR
                writeChan f2p (pid, CPayF2P_Deposit (dl, dr))
    fork $ forever $ do
        CPayF2C_Output (x, y) <- readChan f2c
        ?pass
    return ()

fStateChan :: (MonadFunctionalityAsync m a) => 
    state -> auxin ->
    (forall m'. MonadContract m' => Contract cin cout auxout auxin z m') ->
    (UpdateFunction state (Map PID (Maybe a)) auxin auxout) ->
    Functionality (Either (StateP2F a) cin) (Either (StateF2P state) cout) Void Void Void Void m
fStateChan initState initAuxIn contract update (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
    let sid = ?sid :: SID
    let (parties :: [PID], sssid :: String) = readNote "fStateChannel" $ snd sid
    
    -- state channel variables
    currState :: state <- newIORef initState
    auxIn <- newIORef [initAuxIn]
    inputs <- newIORef $ (Map.empty :: Map Int (IORef (Map PID a)))
    
    let startRound = 0
    round <- newIORef startRound
    ptr <- newIORef 0

    round0Inputs <- newIORef (Map.empty :: Map PID a)
    modifyIORef inputs $ Map.insert startRound round0Inputs
    
    
    -- Init the contract and its channels
    p2f2c :: Chan (PID, cin) <- newChan
    c2f2p :: Chan (PID, cout) <- newChan
    f2c :: Chan auxout <- newChan
    c2f :: Chan auxin <- newChan
    cemit :: Chan z <- newChan  
    passer :: Chan () <- newChan

    let ?pass = writeChan passer () in
                contract (p2f2c, c2f2p) (f2c, c2f) cemit

    let processState = do
        -- set all parties with no input as Nothing
        liftIO $ putStrLn $ "Doing the state update"
        currRound <- readIORef round
        _inputs <- readIORef inputs
        currInputs <- readIORef (_inputs ! currRound)
        _state <- readIORef currState
        _auxin <- readIORef auxIn

        _ptr <- readIORef ptr

        -- set missing inputs to Nothing
        let allInputs = map fillIn parties where
                        fillIn pj
                            | (member pj currInputs) = (pj, Just (currInputs ! pj))
                            | otherwise = (pj, Nothing)
  
        let (_aout, _newState) = update _state (Map.fromList allInputs) (_auxin !! _ptr)  
        liftIO $ putStrLn $ "called state update" 
        writeIORef currState _newState

        -- TODO: in one round if all players are honest in DELTA if not
        liftIO $ putStrLn $ "calling eventually"
        forMseq_ parties $ \pi -> do
            eventually $ writeChan f2p (pi, Left (StateF2P_State _newState))

        -- send auxOut to contract
        liftIO $ putStrLn $ "calling eventually"
        eventually $ writeChan f2c _aout
        
        liftIO $ putStrLn $ "calling eventually"
        eventually $ processState
        ?pass 

    eventually $ processState

    -- incoming messages from parties for contract and F_state
    fork $ forever $ do
        (pid, x) <- readChan p2f
        case x of 
            Right x -> writeChan p2f2c (pid, x)
            Left (StateP2F_Input i) -> do
                -- save all new inputs from parties
                _inputs <- readIORef inputs
                _round <- readIORef round
                let _currRoundInputs = (_inputs ! _round)
                _alreadyInput <- readIORef _currRoundInputs >>= return . member pid
                if _alreadyInput then do
                    liftIO $ putStrLn $ "pid[" ++ show pid ++ "] already gave input"
                    return ()
                else do
                    liftIO $ putStrLn $ "pid[" ++ show pid ++ "] new input"
                    modifyIORef _currRoundInputs $ Map.insert pid i
                ?pass

    -- messages from the contract for the people
    fork $ forever $ do
        (pid, x) <- readChan c2f2p
        writeChan f2p (pid, Right x)

    -- handle auxin
    fork $ forever $ do
        m :: auxin <- readChan c2f
        modifyIORef auxIn $ (++ [m])
        b <- readIORef auxIn >>= return . (+ (-1)) . length
        liftIO $ putStrLn $ "calling aux eventually"
        eventually $ do
            liftIO $ putStrLn $ "andling auxin ptr"
            modifyIORef ptr $ max b 
            ?pass
        ?pass
        
    return ()


testEnvStateChannel :: MonadEnvironment m => Environment 
    (Either (StateF2P PayState) CPayF2P)
    (ClockP2F (Either (StateP2F PayInput) CPayP2F))
    (SttCruptA2Z (Either (StateF2P PayState) CPayF2P) (Either (ClockF2A PayInput) Void)) 
    (SttCruptZ2A (ClockP2F (Either (StateP2F PayInput) CPayP2F)) (Either ClockA2F Void)) 
    Void (ClockZ2F) String m 

testEnvStateChannel z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let extendRight conf = show ("", conf)
    let sid = ("sidStateChannel", show (["Alice", "Bob"], ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty

    latestP <- newIORef Nothing
    latestA <- newIORef Nothing

    fork $ forever $ do
        (pid, m) <- readChan p2z
        liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
        ?pass

    clockChan <- newChan
    fork $ forever $ do 
        mb <- readChan a2z
        ?pass

    -- get current Alice's current deposit
    () <- readChan pump
    writeChan z2p $ ("Alice", ClockP2F_Through (Right (CPayP2F_GetDeposit)))

    -- deposit coins into Alice's balance
    () <- readChan pump
    writeChan z2p $ ("Alice", ClockP2F_Through (Right (CPayP2F_Deposit 10)))
    
    -- get current Alice's current deposit
    () <- readChan pump
    writeChan z2p $ ("Alice", ClockP2F_Through (Right (CPayP2F_GetDeposit)))
    
    () <- readChan pump
    writeChan z2p $ ("Bob", ClockP2F_Through (Right (CPayP2F_Deposit 10)))

    () <- readChan pump
    writeChan z2p $ ("Alice", ClockP2F_Through (Right (CPayP2F_GetDeposit)))
    
    -- give only one input
    () <- readChan pump
    writeChan z2p $ ("Alice", ClockP2F_Through (Left (StateP2F_Input (([1], 0) :: PayInput))))

    -- payment should fail because Bob has no deposit
    () <- readChan pump
    writeChan z2p $ ("Bob", ClockP2F_Through (Left (StateP2F_Input (([2], 0) :: PayInput))))
    
    -- handle the ptr from auxin
    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 1)

    -- do the first state update
    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

    () <- readChan pump
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

    -- force state change with only one input
    () <- readChan pump
    writeChan outp "environment output: 1"

initA = CPayC2F_AuxIn (0,0)
initS = (0, [], 0, [])

testStateChannel :: IO String
testStateChannel = runITMinIO 120 $ execUC testEnvStateChannel (idealProtocol) (runAsyncF (fStateChan initS initA contractPay uPay)) dummyAdversary
    


