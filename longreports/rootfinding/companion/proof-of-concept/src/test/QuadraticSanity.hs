-- | These tests just make sure quadratic formula agrees with companion matrix and hmatrix's eigenvalues.

module QuadraticSanity where

import Companion.Types
import Companion.Coefficients
import Companion.Matrix
import Companion.Invariant

import qualified Data.Vector.Storable as VS
import Numeric.LinearAlgebra

import Test.QuickCheck
