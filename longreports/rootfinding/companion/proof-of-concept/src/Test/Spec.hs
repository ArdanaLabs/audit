-- |

module Main where

import Companion.Types

import Test.Generators
import Test.Quadratic

import Test.QuickCheck

epsilon = 1 / 10 ^ 7

main = do
  quickCheck prop_companionQuadraticNoImaginary
  quickCheck prop_companionQuadraticUniquePosrealRoot
  quickCheck (prop_formulaRootsAreRoots epsilon)
  quickCheck (prop_companionEVsAreRoots epsilon)
  quickCheck (prop_quadraticIsomorphism epsilon)
