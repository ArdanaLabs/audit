-- |

module Companion.Types
  ( Amplification (..)
  , constantAmp
  , D (..)
  , Balances (..)
  , BalanceIdx (..)
  , Coefficient (..)
  , Polynomial (..)
  , deleteIdx
  , polynomialApply
  ) where

newtype Amplification = Amplification { unAmplification :: Double } deriving (Eq, Show)
constantAmp = Amplification 85

newtype D = D { unD :: Double } deriving (Eq, Show)

newtype Balances = Balances { unBalances :: [Double] } deriving (Eq, Show)

newtype BalanceIdx = BalanceIdx { unBalanceIdx :: Int } deriving (Eq, Show)

newtype Coefficient = Coefficient { unCoefficient :: Double } deriving (Eq, Show)

newtype Polynomial = Polynomial { unPolynomial :: [Coefficient] } deriving Eq

instance Show Polynomial where
  show (Polynomial coefs) = foldr (\x y -> x ++ " + " ++ y) ("x^" ++ show n) [
    show (unCoefficient coef) ++ "x^" ++ show k |
    (coef, k) <- zip coefs [0..n - 1]
    ] where n = length coefs

deleteIdx :: Int -> [a] -> [a]
deleteIdx i xs = take i xs ++ drop (i + 1) xs

-- this is a candidate for a lens actually
polynomialApply :: Polynomial -> Double -> Double
polynomialApply (Polynomial p) x =
  foldr (+) (x ^ length p) $ zipWith (*) (map unCoefficient p) [x ^ k | k <- [0..]]
