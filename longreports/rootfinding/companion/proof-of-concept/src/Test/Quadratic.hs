-- | These tests just make sure quadratic formula agrees with companion matrix and hmatrix's eigenvalues.

module Test.Quadratic where

import Data.List (partition)
import Data.Complex
import Control.Monad

import Companion.Types
import Companion.Coefficients
import Companion.Matrix
import Companion.Invariant

import qualified Data.Vector.Storable as VS
import Numeric.LinearAlgebra

import Test.QuickCheck

quadraticFormula :: Polynomial -> Maybe (Double, Double)
quadraticFormula (Polynomial []) = Nothing
quadraticFormula (Polynomial [_]) = Nothing
quadraticFormula (Polynomial (Coefficient u:Coefficient v:[])) = Just $ (p - q, p + q)
  where
    p = - v / 2
    discriminant = v ** 2 - 4 * v
    q = discriminant ** (1 / 2) / 2
quadraticFormula (Polynomial (_:_:_)) = Nothing

-- coefficients of our forms do not give imaginary roots
prop_companionQuadraticNoImaginary k a d balances = length (filter (\r -> imagPart r == 0.0) ev) == length ev
  where
    quadratic = iK k a d balances
    companion = companionK2 quadratic
    ev = VS.toList $ eigenvalues companion
    types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)

-- for coefficients of our forms, there is exactly one positive root
prop_companionQuadraticUniquePosrealRoot k a d balances = length pos == 1 && length neg == 1
  where
    quadratic = iK k a d balances
    companion = companionK2 quadratic
    ev = VS.toList $ eigenvalues companion
    realparts = map realPart ev
    (neg, pos) = partition (< 0) realparts
    types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)

-- WTS that the quadratic formula gives roots that, when evaluated, give zero.
prop_formulaRootsAreRoots epsilon k a d balances = do
  let quadratic = iK k a d balances
  (neg, pos) <- quadraticFormula quadratic
  let negativeRootIsRoot = abs (polynomialApply quadratic neg) < epsilon
      positiveRootIsRoot = abs (polynomialApply quadratic pos) < epsilon
      rootsAreRoots = negativeRootIsRoot && positiveRootIsRoot
  return $ Just rootsAreRoots
  where
    types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)

-- WTS that the companion matrix eigenvalues are roots that, when evaluated, give zero
prop_companionEVsAreRoots epsilon k a d balances = abs zeroNeg < epsilon && abs zeroPos < epsilon
  where
    quadratic = iK k a d balances
    companion = companionK2 quadratic
    ev = VS.toList $ eigenvalues companion
    realparts = map realPart ev
    (neg', pos') = partition (< 0) realparts
    neg = neg' !! 0
    pos = pos' !! 0
    zeroNeg = polynomialApply quadratic neg
    zeroPos = polynomialApply quadratic pos
    types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)


-- WTS that when you traverse Polynomial -> Matrices -> eigenvalues the evs equal Polynomial -> quadraticformula -> roots
prop_quadraticIsomorphism epsilon k a d balances = do
(neg', pos') <- quadraticFormula quadratic
return $ Just ((abs (neg !! 0 - neg') < epsilon) && (abs (pos !! 0 - pos') < epsilon))
where
  quadratic = iK k a d balances
  companion = companionK2 quadratic
  ev = VS.toList $ eigenvalues companion
  realparts = map realPart ev
  (neg, pos) = partition (< 0) realparts
  types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)
