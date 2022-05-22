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

--data CPayP2F = CPayDeposit Int deriving Show
--data CPayF2P = CPayCoins Int deriving Show
--data CPayF2C = CPayOutput (Int, Int) deriving Show
--data CPayC2F = CPayAuxIn (Int, Int) | Ok  deriving Show

type UpdateFunction st inp aux = st -> inp -> aux -> (aux, st)
type PayState = (Int, [Int], Int, [Int]) 
type AuxOutput = (Int, Int)
type AuxInput = (Int, Int)
type PayInput = ([Int], Int)

uPay :: UpdateFunction PayState [PayInput] AuxInput 
uPay state inputs auxIn = ((0,0), (0, [0], 0, [0]))

fStateCPay = fStateChan (0, [], 0, []) (0, 0) (uPay)

fStateChan :: (MonadFunctionalityAsync m a) => 
	PayState -> AuxInput ->
	(UpdateFunction PayState [a] AuxInput) ->
    Functionality (StateP2F a) (StateF2P PayState) Void Void Void Void m
fStateChan initState initAuxIn update (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
    let sid = ?sid :: SID
    let parties :: [PID] = readNote "fStateChannel" $ snd sid

    currState <- newIORef initState
    auxIn <- newIORef [initAuxIn]
    ptr <- newIORef 0
    
    fork $ forever $ do
        (pid, m) <- readChan p2f
        case m of 
            StateP2F_Input x -> do
                ?leak x
                currAuxIn <- readIORef auxIn
                currPtr <- readIORef ptr
                _cstate <- readIORef currState
                let (_aout, _state) = uPay _cstate [x] (currAuxIn !! currPtr)
                writeChan f2p (pid, StateF2P_State _state)
            _ -> return ()
    return ()


testEnvStateChannel :: MonadEnvironment m => Environment 
    (Either (StateF2P Int) ()) 
    (ClockP2F (StateP2F PayInput)) 
    (SttCruptA2Z (StateF2P PayState) (Either (ClockF2A PayInput) Void)) 
    (SttCruptZ2A (ClockP2F (StateP2F PayInput)) (Either ClockA2F Void)) 
    Void (ClockZ2F) String m 

testEnvStateChannel z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let extendRight conf = show ("", conf)
    let sid = ("sidStateChannel", show (["Alice", "Bob"], ""))
    writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty

    fork $ forever $ do
        (pid, m) <- readChan p2z
        ?pass

    clockChan <- newChan
    fork $ forever $ do 
        mb <- readChan a2z
        ?pass

    () <- readChan pump
    writeChan z2p $ ("Alice", ClockP2F_Through (StateP2F_Input ([0], 1)))

    () <- readChan pump
    writeChan outp "environment output: 1"

testStateChannel :: IO String
testStateChannel = runITMinIO 120 $ execUC testEnvStateChannel (idealProtocol) (runAsyncF fStateCPay) dummyAdversary
    


