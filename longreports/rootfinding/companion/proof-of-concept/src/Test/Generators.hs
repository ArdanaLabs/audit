-- |

module Test.Generators where

import Control.Monad

import Companion.Types

import Test.QuickCheck

instance Arbitrary Amplification where
  arbitrary = liftM (Amplification . getPositive) (arbitrary :: Gen (Positive Double))

instance Arbitrary D where
  arbitrary = liftM (D . getPositive) (arbitrary :: Gen (Positive Double))


instance Arbitrary Balances where
  arbitrary = liftM (Balances . (map getPositive)) (vectorOf 8 (arbitrary :: Gen (Positive Double)))

instance Arbitrary BalanceIdx where
  arbitrary = liftM BalanceIdx $ elements [0..8 - 1]

-- no more than 10 assets
--arbBalances :: Int -> Gen Balances
--arbBalances 0 = (liftM Balances []) :: Gen Balances
--arbBalances n = do
--  f <- replicateM (n - 1) arbBalances (n - 1)
--  return $ Balances f

--instance Arbitrary Balances where
--  arbitrary = sized arbBalances
