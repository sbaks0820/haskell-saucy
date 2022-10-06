 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, RankNTypes
  #-} 

module ACastCheck where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import ACast

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
import TestTools
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

propIdealACastSafetyEnv
  :: MonadEnvironment m =>
  Environment (ACastF2P String) (ClockP2F (ACastP2F String)) (SttCruptA2Z a (Either (ClockF2A String) Void)) (SttCruptZ2A b (Either ClockA2F Void)) Void (ClockZ2F) String m
propIdealACastSafetyEnv z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)

  -- choose the parties and the leader  
  n <- liftIO $ (generate $ choose (4,100))
  let parties = fmap show [1..n]

  leader <- liftIO $ (generate $ choose (4,n)) >>= return . show
    
  let t :: Int = if ((n `div` 3) * 3) < n then (n `div` 3)
                 else (n `div` 3)-1
 
  let sid = ("sidtestacast", show (leader, parties, t, "")) 

  --let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    printEnvIdeal $ "[testEnvACastIdeal]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p (leader, ClockP2F_Through $ ACastP2F_Input ("I'm " ++ leader))

  -- Empty the queue
  let checkQueue = do
        writeChan z2a $ SttCruptZ2A_A2F (Left ClockA2F_GetCount)
        mb <- readChan a2z
        let SttCruptA2Z_F2A (Left (ClockF2A_Count c)) = mb
        liftIO $ putStrLn $ "Z[testEnvACastIdeal]: Events remaining: " ++ show c
        return (c > 0)

  () <- readChan pump
  whileM_ checkQueue $ do
    {- Two ways to make progress -}
    {- 1. Environment to Functionality - make progress -}
    -- writeChan z2f ClockZ2F_MakeProgress
    {- 2. Environment to Adversary - deliver the next message -}
    writeChan z2a $ SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))
    readChan pump

  writeChan outp "environment output: 1"

prop_dumySafety = monadicIO $ do
    t <- run $ runITMinIO 120 $ execUC propIdealACastSafetyEnv (idealProtocol) (runAsyncF $ fACast) dummyAdversary
    let x :: String = show t
    assert (1 == 1) 

runqueueExecList :: Int -> Gen [Int]
runqueueExecList n = frequency
    [ (1,return []),
      (5, if n==0 then return [] else (:) <$> choose (0,n-1)  <*> (runqueueExecList (n-1)))
    ] 

data ACastCmd = CmdVAL SID PID String | CmdECHO SID PID String | CmdREADY SID PID String | CmdDeliver Int | CmdGetCount deriving Show

-- SID, Parties, Crupt, t < n/3, leader
type ACastConfig = (SID, [PID], Map PID (), Int, PID)

performACastEnv 
  :: (MonadEnvironment m) => 
  ACastConfig -> [ACastCmd] ->
  (Environment (ACastF2P String) (ClockP2F (ACastP2F String))
     (SttCruptA2Z (SID, MulticastF2P (ACastMsg String)) (Either (ClockF2A (SID, ACastMsg String)) (SID, MulticastF2A (ACastMsg String))))
     (SttCruptZ2A (ClockP2F (SID, ACastMsg String)) (Either ClockA2F (SID, MulticastA2F (ACastMsg String)))) Void
     (ClockZ2F) Transcript m)
performACastEnv aCastConfig cmdList z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let (sid :: SID, parties :: [PID], crupt :: Map PID (), t :: Int, leader :: PID) = aCastConfig 
    writeChan z2exec $ SttCrupt_SidCrupt sid crupt

    transcript <- newIORef []
    fork $ forever $ do
      (pid, m) <- readChan p2z
      modifyIORef transcript (++ [Right (pid, m)])
      --printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
      ?pass

    clockChan <- newChan
    fork $ forever $ do
      mb <- readChan a2z
      modifyIORef transcript (++ [Left mb])
      case mb of
        SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
          printEnvReal $ "Pass"
          ?pass
        SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
          writeChan clockChan c
        SttCruptA2Z_P2A (pid, m) -> do
          case m of
            _ -> do
              printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
          ?pass
        SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
          --printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
          ?pass
        _ -> error $ "Help!" ++ show mb
        
    () <- readChan pump 

    forMseq_ cmdList $ \cmd -> do
        case cmd of
            CmdVAL ssid' pid' m' -> do
                writeChan z2a $ SttCruptZ2A_A2F $ Right (ssid', MulticastA2F_Deliver pid' (ACast_VAL m')) 
                readChan pump
            CmdECHO ssid' pid' m' -> do
                writeChan z2a $ SttCruptZ2A_A2F $ Right (ssid', MulticastA2F_Deliver pid' (ACast_ECHO m'))
                readChan pump
            CmdREADY ssid' pid' m' -> do
                writeChan z2a $ SttCruptZ2A_A2F $ Right (ssid', MulticastA2F_Deliver pid' (ACast_READY m'))
                readChan pump
            CmdDeliver idx' -> do
                writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')
                readChan pump
            CmdGetCount -> do     
                writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetCount
                readChan clockChan
                return ()
    writeChan outp =<< readIORef transcript

propEnvBrachaSafety
  :: (MonadEnvironment m) =>
  Environment (ACastF2P String) (ClockP2F (ACastP2F String))
     (SttCruptA2Z (SID, MulticastF2P (ACastMsg String)) (Either (ClockF2A (SID, ACastMsg String)) (SID, MulticastF2A (ACastMsg String))))
     (SttCruptZ2A (ClockP2F (SID, ACastMsg String)) (Either ClockA2F (SID, MulticastA2F (ACastMsg String)))) Void
     (ClockZ2F) (ACastConfig, [ACastCmd], Transcript) m
propEnvBrachaSafety z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave"]
  let leader = "Alice"
  let t = 1 :: Int
  let crupt = Map.fromList [("Alice",())] :: Map PID () 
  let sid = ("sidTestACast", show (leader, parties, t, ""))

  -- compute ssids
  let ssidAlice1 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "1"))
  let ssidAlice2 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "2"))
  let ssidAlice3 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "3"))
  
  writeChan z2exec $ SttCrupt_SidCrupt sid crupt

  transcript <- newIORef []
  cmdList <- newIORef []
  
  fork $ forever $ do
    (pid, m) <- readChan p2z
    modifyIORef transcript (++ [Right (pid, m)])
    --printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  clockChan <- newChan
  fork $ forever $ do
    mb <- readChan a2z
    modifyIORef transcript (++ [Left mb])
    case mb of
      SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
        printEnvReal $ "Pass"
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
        writeChan clockChan c
      SttCruptA2Z_P2A (pid, m) -> do
        case m of
          _ -> do
            printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
        --printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
        ?pass
      _ -> error $ "Help!" ++ show mb

  () <- readChan pump
  -- Select a set of parties and select one of 0 and 1 for each VAL message
  to_send_val <- selectPIDs parties
  printYellow ("\nParties: " ++ show to_send_val ++ "\n")

  -- send VAL to each of the with one of [0,1] as the value
  forMseq_ [0..(length to_send_val)-1] $ \i -> do
    this_val <- liftIO $ (generate $ choose (0 :: Int, 1 :: Int)) >>= return . show 
    writeChan z2a $ SttCruptZ2A_A2F $ Right (ssidAlice1, MulticastA2F_Deliver (to_send_val !! i) (ACast_VAL this_val))
    modifyIORef cmdList $ (++) [CmdVAL ssidAlice1 (to_send_val !! i) this_val]
    () <- readChan pump
    return ()

  -- get the number of things in the runqueue
  writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetCount
  num <- readChan clockChan
  idxToDeliver <- liftIO $ generate $ runqueueExecList num  
  modifyIORef cmdList $ (++) [CmdGetCount]


  -- deliver the indices
  forMseq_ [0..(length idxToDeliver)-1] $ \i -> do
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver (idxToDeliver !! i))
    modifyIORef cmdList $ (++) [CmdDeliver (idxToDeliver !! i)]
    () <- readChan pump
    return ()

  -- do the same with ECHO
  to_send_echo <- selectPIDs parties 
  printYellow ("\nParties: " ++ show to_send_echo ++ "\n")
  
  -- send VAL to each of the with one of [0,1] as the value
  forMseq_ [0..(length to_send_echo)-1] $ \i -> do
    this_val <- liftIO $ (generate $ choose (0 :: Int, 1 :: Int)) >>= return . show 
    writeChan z2a $ SttCruptZ2A_A2F $ Right (ssidAlice2, MulticastA2F_Deliver (to_send_echo !! i) (ACast_ECHO this_val))
    modifyIORef cmdList $ (++) [CmdECHO ssidAlice2 (to_send_echo !! i) this_val]
    () <- readChan pump
    return ()

  -- get the number of things in the runqueue
  writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetCount
  num <- readChan clockChan
  idxToDeliver <- liftIO $ generate $ runqueueExecList num
  modifyIORef cmdList $ (++) [CmdGetCount]

  -- deliver the indices
  forMseq_ [0..(length idxToDeliver)-1] $ \i -> do
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver (idxToDeliver !! i))
    modifyIORef cmdList $ (++) [CmdDeliver (idxToDeliver !! i)]
    () <- readChan pump
    return ()
  
  -- do the same with READY
  to_send_ready <- selectPIDs parties 
  printYellow ("\nParties: " ++ show to_send_ready ++ "\n")
  
  -- send VAL to each of the with one of [0,1] as the value
  forMseq_ [0..(length to_send_ready)-1] $ \i -> do
    this_val <- liftIO $ (generate $ choose (0 :: Int, 1 :: Int)) >>= return . show 
    writeChan z2a $ SttCruptZ2A_A2F $ Right (ssidAlice3, MulticastA2F_Deliver (to_send_ready !! i) (ACast_READY this_val))
    modifyIORef cmdList $ (++) [CmdREADY ssidAlice3 (to_send_ready !! i) this_val]
    () <- readChan pump
    return ()

  -- get the number of things in the runqueue
  writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetCount
  num <- readChan clockChan
  idxToDeliver <- liftIO $ generate $ runqueueExecList num  
  modifyIORef cmdList $ (++) [CmdGetCount]

  -- deliver the indices
  forMseq_ [0..(length idxToDeliver)-1] $ \i -> do
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver (idxToDeliver !! i))
    modifyIORef cmdList $ (++) [CmdDeliver (idxToDeliver !! i)]
    () <- readChan pump
    return ()

  -- deliver any remaining messages
  writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetCount
  num <- readChan clockChan
  modifyIORef cmdList $ (++) [CmdGetCount]

  forMseq_ (reverse [0..num-1]) $ \i -> do
    idx <- liftIO $ generate $ choose (0,i)
    writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx)  
    modifyIORef cmdList $ (++) [CmdDeliver idx]
    () <- readChan pump
    return ()

  tr <- readIORef transcript
  cl <- readIORef cmdList
  --writeChan outp =<< readIORef transcript
  writeChan outp ((sid, parties, crupt, t, leader), reverse cl, tr)

prop_brachaSafety = monadicIO $ do
    (config', c', t') <- run $ runITMinIO 120 $ execUC propEnvBrachaSafety (runAsyncP protACast) (runAsyncF $ bangFAsync fMulticast) dummyAdversary
    t <- run $ runITMinIO 120 $ execUC (performACastEnv config' c') (runAsyncP protACast) (runAsyncF $ bangFAsync fMulticast) dummyAdversary
    --assert (t == [])
    let x :: String = show t
    -- require that all deliverances are the same
    outputs <- newIORef Set.empty
    forMseq_ [0..(length t)-1] $ \i -> do
        case (t !! i) of 
            Right (pid, ACastF2P_Deliver m) -> 
                modifyIORef outputs $ Set.insert m
            Left m -> return ()
    o <- readIORef outputs

    printYellow ("[Config]\n\n" ++ show config')
    printYellow ("[Inputs]\n\n" ++ show c')
    assert ( (Set.size o) <= 1 )
                

--prop_brachaSafety = monadicIO $ do
--  (t1 :: Transcript, t2 :: Transcript) <- run $ runITMinIO 120 $ do
--    liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
--    t1R <- runRandRecord $ execUC
--               propEnvBrachaSafety
--               (runAsyncP protACastBroken) 
--               (runAsyncF $ bangFAsync fMulticast)
--               dummyAdversary
--    let (t1, bits) = t1R
--    liftIO $ putStrLn ""
--    liftIO $ putStrLn ""  
--    liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
--    t2 <- runRandReplay bits $ execUC
--               propEnvBrachaSafety
--               (idealProtocol) 
--               (runAsyncF $ fACast)
--               simACast
--    --assert (t1 == t2)
--    return (t1, t2)
--  assert (t1==t2)

--testCompareBroken :: IO Bool
--testCompareBroken = runITMinIO 120 $ do
--  liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
--  t1R <- runRandRecord $ execUC
--             testEnvACastBroken 
--             (runAsyncP protACastBroken) 
--             (runAsyncF $ bangFAsync fMulticast)
--             dummyAdversary
--  let (t1, bits) = t1R
--  liftIO $ putStrLn ""
--  liftIO $ putStrLn ""  
--  liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
--  t2 <- runRandReplay bits $ execUC
--             testEnvACastBroken 
--             (idealProtocol) 
--             (runAsyncF $ fACast)
--             simACast
--  return (t1 == t2)




