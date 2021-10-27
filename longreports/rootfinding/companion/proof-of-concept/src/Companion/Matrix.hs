-- |

module Companion.Matrix where

import Companion.Types

import Numeric.LinearAlgebra

-- special case
identity' :: Int -> [[Double]]
identity' n =  [
  replicate k 0 ++ [1] ++ replicate (n - 1 - k) 0 | k <- [0..n - 1]
  ]
companionD4 :: Polynomial -> Matrix Double
companionD4 (Polynomial (Coefficient s:Coefficient t:_)) = (4><4)
  (replicate (4 - 1) 0 ++ [- s]
  ++
  [1] ++ replicate (4 - 2) 0 ++ [- t]
  ++
  [0, 1] ++ replicate (4 - 2) 0
  ++
  [0, 0, 1] ++ replicate (4 - 3) 0)

companionD3 :: Polynomial -> Matrix Double
companionD3 (Polynomial (Coefficient s:Coefficient t:_)) = (3><3) [0,0,-s, 1,0,-t, 0,1,0]

companionD2 :: Polynomial -> Matrix Double
companionD2 (Polynomial (Coefficient u:Coefficient v:[])) = (2><2) [0,-u, 1,-v]

companionIxi :: Double -> Double -> [[Double]]
companionIxi u v = [[0, - v], [1, - u]]
