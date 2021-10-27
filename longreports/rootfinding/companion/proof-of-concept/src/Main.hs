module Main where

import Data.Complex

import qualified Data.Vector.Storable as VS
import Numeric.LinearAlgebra

import Companion.Types
import Companion.Coefficients
import Companion.Matrix
import Companion.Invariant

-- unit test
a = constantAmp
d = D 228616770440.3383
balances = Balances [114425339047.88353, 114097008086.95198, 115039925432.79308]
k = BalanceIdx 1

-- unittest polynomialApply
testInp1 = Polynomial [Coefficient 1, Coefficient 2, Coefficient 3]
testOutp1 = polynomialApply testInp1 9

main :: IO ()
main = do
  -- print $ Polynomial [balanceConstantTerm k a d balances, balanceLinearTerm k a d balances]
  let iD3 = iD a balances
  print ("Invariant polynomial for three balances = " ++ show iD3)
  putStr "C(I_D^3) = "
  print $ companionD4 iD3
  let roots = VS.toList $ eigenvalues $ companionD4 iD3
      acomplexRoots = filter (\r -> imagPart r == 0.0) roots
      realPartsAcomplexRoots = map realPart acomplexRoots
  -- Should have exactly one posreal root
  print $ "should be true: " ++ show (length (filter (>0) realPartsAcomplexRoots) == 1)
  let shouldAllBeZero = map (polynomialApply iD3) realPartsAcomplexRoots
  print $ zip realPartsAcomplexRoots shouldAllBeZero
  print (testOutp1 == 1 + 2 * 9 + 3 * 9 ^ 2 + 9 ^ 3)
