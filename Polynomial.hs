{-# LANGUAGE DataKinds, FlexibleInstances, MultiParamTypeClasses,
             OverloadedLists, PatternSynonyms
#-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ParallelListComp #-}

module Polynomial where

import Data.List (tails)
import Data.Poly
import Data.Vector (forM,fromList)
import Data.Field.Galois (Prime, toP)
import ProcessIO
import System.Random

type Fq = Prime 53

three :: Fq
three = 3

type PolyFq = VPoly Fq


-- Random field element
randFq :: MonadITM m => m Fq
randFq = getNbits 120 >>= return . toP

-- Build poly from coefficients
polyFromCoeffs :: [Fq] -> PolyFq
polyFromCoeffs = toPoly . fromList 

randomDegree :: MonadITM m => Int -> m PolyFq
randomDegree t = forM [0..t] (\_ -> randFq) >>= return . toPoly

testp :: PolyFq
testp = toPoly [1,2,3]

test1 = runITMinIO 120 $ randomDegree 5

-- evalPoly
test2' = runITMinIO 120 $ do
  f <- randomDegree 5
  return $ eval f 0

  
-- Add multiple polys
test3 = testp + testp

-- Interpolate
test4 = polyInterp [(0,2),(1,4)] three

_t1 :: Fq
_t1 = 2
_t2 :: PolyFq
_t2 = toPoly [1,2,3]
test5 = [_t1] * _t2

-- Lagrange interpolation

-- This is taken from polynomial package,
-- https://hackage.haskell.org/package/polynomial-0.7.3/docs/src/Math-Polynomial-Interpolation.html#polyInterp

-- |Evaluate a polynomial passing through the specified set of points.  The
-- order of the interpolating polynomial will (at most) be one less than 
-- the number of points given.
polyInterp :: Fractional a => [(a,a)] -> a -> a
polyInterp xys = head . last . neville xys

-- |Computes the tableau generated by Neville's algorithm.  Each successive
-- row of the table is a list of interpolants one order higher than the previous,
-- using a range of input points starting at the same position in the input
-- list as the interpolant's position in the output list.
neville :: Fractional a => [(a,a)] -> a -> [[a]]
neville xys x = table
    where
        (xs,ys) = unzip xys
        table = ys :
            [ [ ((x - x_j) * p1 + (x_i - x) * p0) / (x_i - x_j)
              | p0:p1:_ <- tails row
              | x_j     <- xs
              | x_i     <- x_is
              ]
            | row  <- table
            | x_is <- tail (tails xs)
            , not (null x_is)
            ]