-- |

module Companion.Matrix
  ( companionD4
  , companionD3
  , companionK2
  ) where

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

companionK2 :: Polynomial -> Matrix Double
companionK2 (Polynomial (Coefficient u:Coefficient v:[])) = (2><2) [0,-u, 1,-v]
