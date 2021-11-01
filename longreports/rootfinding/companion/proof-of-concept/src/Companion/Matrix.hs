-- |

module Companion.Matrix (companion) where

import Companion.Types

import Numeric.LinearAlgebra

companion :: Polynomial -> Matrix Double
companion (Polynomial []) = (0><0) []
companion (Polynomial xs) = (n><n)
  (replicate (n - 1) 0 ++ [- (unCoefficient $ head xs)]
  ++
  concat [replicate k 0 ++ [1] ++ replicate (n - 2 - k) 0 ++ [- unCoefficient x'] | (k, x') <- zip [0..] (tail xs)])
  where n = length xs
        z = Coefficient 0
        o = Coefficient 1

