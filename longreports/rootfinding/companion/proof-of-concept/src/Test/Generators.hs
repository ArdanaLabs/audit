-- |

module Test.Generators where

import Control.Monad

import Companion.Types

import Test.QuickCheck

instance Arbitrary Amplification where
  arbitrary = liftM (Amplification . getPositive) (arbitrary :: Gen (Positive Double))

instance Arbitrary D where
  arbitrary = liftM (D . getPositive) (arbitrary :: Gen (Positive Double))

numAssets = 8

instance Arbitrary Balances where
  arbitrary = liftM (Balances . (map getPositive)) (vectorOf numAssets (arbitrary :: Gen (Positive Double)))

instance Arbitrary BalanceIdx where
  arbitrary = liftM BalanceIdx $ elements [0..numAssets - 1]

-- no more than 10 assets
--arbBalances :: Int -> Gen Balances
--arbBalances 0 = (liftM Balances []) :: Gen Balances
--arbBalances n = do
--  f <- replicateM (n - 1) arbBalances (n - 1)
--  return $ Balances f

--instance Arbitrary Balances where
--  arbitrary = sized arbBalances
