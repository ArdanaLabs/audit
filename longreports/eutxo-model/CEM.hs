module CEM where
-- Constraint emitter machines from https://iohk.io/en/research/library/papers/the-extended-utxo-model/

import Control.Monad
import Control.Lens

type Quantity = Double
type Tick = Int
type Address = Int

type TxId = Int


newtype S = Char
newtype I = Int

newtype

newtype TxConstraints = Tx -> Bool
