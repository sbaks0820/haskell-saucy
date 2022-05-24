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
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map

data StateP2F a = StateP2F_Input a deriving Show
data StateF2P a = StateF2P_State a deriving Show

data CPayP2F = CPayP2F_Deposit Int | CPayP2F_GetDeposit deriving Show
data CPayF2P = CPayF2P_Deposit (Int, Int) deriving Show
data CPayF2C = CPayF2C_Output AuxOutput deriving Show
data CPayC2F = CPayC2F_AuxIn AuxInput | CPayC2F_Ok  deriving Show


type UpdateFunction st inp aux = st -> inp -> aux -> (aux, st)


--contractPay :: MonadContract m => Contract CPayP2F CPayF2P CPayF2C CPayC2F () m
--contractPay (p2f, f2p) (f2c, c2f) emit = do
--    depositsL <- newIORef 0
--    depositsR <- newIORef 0
--
--    fork $ forever $ do
--        --(pid, CPayDeposit x) <- readChan p2f
--        (pid, m) <- readChan p2f
--        case m of
--            CPayP2F_Deposit x -> do
--                if pid == "Alice" then do
--                    modifyIORef depositsL $ (+) x
--                else if pid == "Bob" then do
--                    modifyIORef depositsR $ (+) x
--                else error "who is this person?"
--                dl <- readIORef depositsL
--                dr <- readIORef depositsR
--                writeChan c2f (CPayC2F_AuxIn (dl, dr))
--            CPayP2F_GetDeposit -> do
--                dl <- readIORef depositsL
--                dr <- readIORef depositsR
--                writeChan f2p (pid, CPayF2P_Deposit (dl, dr))
--    fork $ forever $ do
--        CPayF2C_Output (x, y) <- readChan f2c
--        writeChan c2f CPayC2F_Ok
--    return ()

--uPay :: (Int, [Int], Int, [Int]) -> [([Int], Int)] -> (Int, Int) -> ((Int, Int), (Int, [Int], Int, [Int]))
uPay :: UpdateFunction (Int, [Int], Int, [Int]) [([Int], Int)] (Int, Int)
uPay state inputs auxIn = do
    let zero :: Int = 0
    --return ( (zero, zero),  (zero, [zero], zero, [zero]) )
    ( (zero, zero), (zero, [], zero, []) )

--fStateCPay :: (MonadFunctionalityAsync m a) => Functionality (Either (StateP2F a) CPayP2F) (Either (StateF2P (Int, [Int], Int, [Int])) CPayF2P) Void Void Void Void m
--fStateCPay :: (MonadFunctionalityAsync m a) => Functionality (Either (StateP2F a) Int) (Either (StateF2P (Int, [Int], Int, [Int])) Int) Void Void Void Void m
--fStateCPay = fStateChan (0, [], 0, []) (0, 0) (contractPay) (uPay)
fStateCPay = fStateChan (0, [], 0, []) (0, 0) (uPay)

--runContract :: MonadFunctionalityAsync m l => (MonadContract m' => Contract x y z m') -> Chan (PID, x) -> Chan (PID, y) -> Chan z -> m ()
--runContract contract p2f2c c2f2p f2c = do
--  let ?emit = return () in
--              let ?send = return () in contract (p2f2c, c2f2p) f2c    
--  return ()

-- for cpay
-- cin=CPayP2F Int   cout=CPayF2P Int
-- auxout=CPayF2C    auxin=CPayC2F
-- z=()
-- state=(Int, [Int], Int, [Int])
-- a=Int
-- 
fStateChan :: (MonadFunctionalityAsync m a) =>
    state -> aux ->
    --(forall m'. MonadContract m' => Contract cin cout auxout auxin z m') ->
    --(state -> [a] -> ain -> (auxout, state)) -> 
	(UpdateFunction state [a] aux) ->
    Functionality (Either (StateP2F a) aux) (Either (StateF2P state) cout) Void Void Void Void m
fStateChan initState initAuxIn update (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
    let sid = ?sid :: SID
    let parties :: [PID] = readNote "fStateChannel" $ snd sid

    currState <- newIORef initState
    auxIn <- newIORef [initAuxIn]
    ptr <- newIORef 0

    --p2f2c :: Chan (PID, cin) <- newChan 
    --c2f2p :: Chan (PID, cout) <- newChan
    --f2c :: Chan auxout <- newChan
    --c2f :: Chan auxin <- newChan
    --cemit :: Chan z <- newChan
   
    --contract (p2f2c, c2f2p) (f2c, c2f) cemit

    --let initUPay = uPay (readIORef currState)


    --let (_aout :: auxout, _state) = uPay (0, [0], 0, [0]) [([0],0)] (0,0)

    fork $ forever $ do
        (pid, m) <- readChan p2f
        case m of 
            Left (StateP2F_Input x) -> do
                ?leak x
                currAuxIn <- readIORef auxIn
                currPtr <- readIORef ptr
                _cstate <- readIORef currState
                let (_aout, _state) = uPay _cstate [x] (currAuxIn !! currPtr)
                writeChan f2p (pid, Left (StateF2P_State _state))
                --writeChan f2p (pid, Left (StateF2P_State x))
            _ -> return ()
    return ()


testEnvStateChannel :: MonadEnvironment m => Environment 
    (Either (StateF2P Int) Int) 
    (ClockP2F (Either (StateP2F Int) Int)) 
    (SttCruptA2Z (Either (StateF2P Int) Int) (Either (ClockF2A Int) Void)) 
    (SttCruptZ2A (ClockP2F (Either (StateP2F Int) Int)) (Either ClockA2F Void)) 
    Void (ClockZ2F) String m 

testEnvStateChannel z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let extendRight conf = show ("", conf)
    let sid = ("sidStateChannel", show (["Alice", "Bob"], ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty

    transcript <- newIORef []

    fork $ forever $ do
        (pid, m) <- readChan p2z
        printEnvIdeal $ "[testEnvState]: pid[" ++ pid ++ "] output " ++ show m
        ?pass

    clockChan <- newChan
    fork $ forever $ do 
        mb <- readChan a2z
        modifyIORef transcript (++ [Left mb])
        ?pass
        case mb of
            SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
                printEnvReal $ "Pass"
                ?pass
            SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
                writeChan clockChan c
            SttCruptA2Z_P2A (pid, m) -> do
                case m of
                    _ -> do printEnvReal $ "[" ++ pid ++ "] (corrupt) received: " ++ show m
                ?pass
            SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
                printEnvIdeal $ "[testEnvState leaks]: " ++ show l
                ?pass
            _ -> error $ "Help! " ++ show mb


    () <- readChan pump
    writeChan z2p $ ("Alice", ClockP2F_Through (Left (StateP2F_Input ([], 1))))

    () <- readChan pump
    writeChan outp "environment output: 1"

testStateChannel :: IO String
testStateChannel = runITMinIO 120 $ execUC testEnvStateChannel (idealProtocol) (runAsyncF fStateCPay) dummyAdversary
    


