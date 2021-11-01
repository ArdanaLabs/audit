-- | These tests just make sure quadratic formula agrees with companion matrix and hmatrix's Mat.eigenvalues.

module Test.Quadratic where

import Data.List (partition)
import Data.Complex
import Control.Monad

import Companion.Types
import Companion.Coefficients
import Companion.Matrix
import Companion.Invariant

import qualified Data.Vector.Storable as VS
import qualified Numeric.LinearAlgebra as Mat

import Test.QuickCheck

quadraticFormula :: Polynomial -> Maybe (Double, Double)
quadraticFormula (Polynomial []) = Nothing
quadraticFormula (Polynomial [_]) = Nothing
quadraticFormula (Polynomial [Coefficient u,Coefficient v]) = Just (p - q, p + q)
  where
    p = - v / 2
    discriminant = v ** 2 - 4 * v
    q = discriminant ** (1 / 2) / 2
quadraticFormula (Polynomial (_:_:_)) = Nothing

-- multiply root by by (V + sqrt(discriminant))/(V + sqrt(discriminant))
quadraticFormula' :: Polynomial -> Maybe (Double, Double)
quadraticFormula' (Polynomial []) = Nothing
quadraticFormula' (Polynomial [_]) = Nothing
quadraticFormula' (Polynomial [Coefficient u,Coefficient v]) = Just (neg, pos)
  where
    discriminant = v ** 2 - 4 * v
    pos = - 2 * u / (v + discriminant ** (1 / 2))
    neg = - (v + discriminant ** (1 / 2)) / 2
quadraticFormula' (Polynomial (_:_:_)) = Nothing


-- coefficients of our forms do not give imaginary roots
prop_companionQuadraticNoImaginary k a d balances = length (filter (\r -> imagPart r == 0.0) ev) == length ev
  where
    quadratic = iK k a d balances
    companion' = companion quadratic
    ev = VS.toList $ Mat.eigenvalues companion'
    types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)

-- for coefficients of our forms, there is exactly one positive root
prop_companionQuadraticUniquePosrealRoot k a d balances = length pos == 1 && length neg == 1
  where
    quadratic = iK k a d balances
    companion' = companion quadratic
    ev = VS.toList $ Mat.eigenvalues companion'
    realparts = map realPart ev
    (neg, pos) = partition (< 0) realparts
    types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)

-- WTS that the quadratic formula gives roots that, when evaluated, give zero.
prop_formulaRootsAreRoots epsilon k a d balances = do
  let quadratic = iK k a d balances
  (neg, pos) <- quadraticFormula' quadratic
  let negativeRootIsRoot = abs (polynomialApply quadratic neg) < epsilon
      positiveRootIsRoot = abs (polynomialApply quadratic pos) < epsilon
      rootsAreRoots = negativeRootIsRoot && positiveRootIsRoot
  return $ Just rootsAreRoots
  where
    types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)

-- WTS that the companion matrix Mat.eigenvalues are roots that, when evaluated, give zero
prop_companionEVsAreRoots epsilon k a d balances = abs zeroNeg < epsilon && abs zeroPos < epsilon
  where
    quadratic = iK k a d balances
    companion' = companion quadratic
    ev = VS.toList $ Mat.eigenvalues companion'
    realparts = map realPart ev
    (neg', pos') = partition (< 0) realparts
    neg = head neg'
    pos = head pos'
    zeroNeg = polynomialApply quadratic neg
    zeroPos = polynomialApply quadratic pos
    types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)


-- WTS that when you traverse Polynomial -> Matrices -> Mat.eigenvalues the evs equal Polynomial -> quadraticformula -> roots
prop_quadraticIsomorphism epsilon k a d balances = do
  (neg', pos') <- quadraticFormula' quadratic
  return $ Just ((abs (head neg - neg') < epsilon) && (abs (head pos - pos') < epsilon))
  where
    quadratic = iK k a d balances
    companion' = companion quadratic
    ev = VS.toList $ Mat.eigenvalues companion'
    realparts = map realPart ev
    (neg, pos) = partition (< 0) realparts
    types = (k :: BalanceIdx, a :: Amplification, d :: D, balances :: Balances)

-- Theorem 3.3.14. Every monic polynomial is both the minimal polynomial and the characteristic polynomial of its companion matrix.
-- horn and johnson
--atrixPower :: Mat.Numeric a => Mat.Matrix a -> Int -> Mat.Matrix a
--atrixPower a n = foldr (Mat.<>) (Mat.ident (floor (length $ concat $ Mat.toLists a) ** (1 / 2))) (replicate n a)
--olynomialApplyMatrix :: Polynomial -> Mat.Matrix Double -> Mat.Matrix Double
--olynomialApplyMatrix (Polynomial p) a =
-- foldr
-- (Mat.add)
-- (matrixPower a $ length p)
-- (
--   zipWith ((Mat.*) :: Double -> Mat.Matrix Double -> Mat.Matrix Double)
--   (map unCoefficient p)
--   [matrixPower a k :: Mat.Matrix Double | k <- [0..]]
-- )
--rop_companionAnnihilated epsilon k a d balances = do
-- let quadratic = iK k a d balances
--     companion' = companion quadratic
--     shouldBeZeros = polynomialApplyMatrix quadratic companion'
-- return $ Just all (== 0.0) $ concat $ Mat.toLists shouldBeZeros
