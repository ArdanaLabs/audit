-- |

module Companion.Coefficients
  ( balanceConstantTerm
  , balanceLinearTerm
  , dConstantTerm
  , dLinearTerm
  ) where

import Companion.Types

-- u
balanceConstantTerm :: BalanceIdx -> Amplification -> D -> Balances -> Coefficient
balanceConstantTerm (BalanceIdx k) (Amplification a) (D d) (Balances balances) =
  Coefficient (- d ** (n + 1) / a / n ** (2 * n) / product (deleteIdx k balances))
  where
    n = fromIntegral $ length balances

-- v
balanceLinearTerm :: BalanceIdx -> Amplification -> D -> Balances -> Coefficient
balanceLinearTerm (BalanceIdx k) (Amplification a) (D d) (Balances balances) =
  Coefficient (sum (deleteIdx k balances) + (1 / a / n ** n - 1) * d)
  where
    n = fromIntegral $ length balances

-- s
dConstantTerm :: Amplification -> Balances -> Coefficient
dConstantTerm (Amplification a) (Balances balances) =
  Coefficient (- a * n ** (2 * n) * product balances * sum balances) where n = fromIntegral $ length balances

-- t
dLinearTerm :: Amplification -> Balances -> Coefficient
dLinearTerm (Amplification a) (Balances balances) =
  Coefficient ((a + 1 / n ** n) * n ** (2 * n) * product balances) where n = fromIntegral $ length balances
