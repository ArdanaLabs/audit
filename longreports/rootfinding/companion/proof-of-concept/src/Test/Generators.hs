-- |

module Test.Generators where

import Companion.Types

import Test.QuickCheck

instance Arbitrary Amplification where
  arbitrary = fmap (Amplification . getPositive) (arbitrary :: Gen (Positive Double))

instance Arbitrary D where
  arbitrary = fmap (D . getPositive) (arbitrary :: Gen (Positive Double))

numAssets = 3

instance Arbitrary Balances where
  arbitrary = fmap (Balances . map getPositive) (vectorOf numAssets (arbitrary :: Gen (Positive Double)))

instance Arbitrary BalanceIdx where
  arbitrary = BalanceIdx <$> elements [0..numAssets - 1]

-- no more than 10 assets
--arbBalances :: Int -> Gen Balances
--arbBalances 0 = (fmap Balances []) :: Gen Balances
--arbBalances n = do
--  f <- replicateM (n - 1) arbBalances (n - 1)
--  return $ Balances f

--instance Arbitrary Balances where
--  arbitrary = sized arbBalances
