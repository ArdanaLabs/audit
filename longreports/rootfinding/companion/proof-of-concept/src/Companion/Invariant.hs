-- |

module Companion.Invariant
  ( iD
  , iK
  ) where

import Companion.Types
import Companion.Coefficients

iD :: Amplification -> Balances -> Polynomial
iD a (Balances balances) =
  Polynomial ([dConstantTerm a (Balances balances), dLinearTerm a (Balances balances)] ++ replicate (length balances + 1 - 2) (Coefficient  0))

iK :: BalanceIdx -> Amplification -> D -> Balances -> Polynomial
iK k a d balances =
  Polynomial [balanceConstantTerm k a d balances, balanceLinearTerm k a d balances]
