-- |

module Main where

import Companion.Types

import Test.Generators
import Test.Quadratic

import Test.QuickCheck

precisionOOM = 128
epsilon = 1 / 10 ^ precisionOOM

maxTests = 10000

main = do
  quickCheck (withMaxSuccess maxTests prop_companionQuadraticNoImaginary)
  quickCheck (withMaxSuccess maxTests prop_companionQuadraticUniquePosrealRoot)
  quickCheck (withMaxSuccess maxTests (prop_formulaRootsAreRoots epsilon))
  quickCheck (withMaxSuccess maxTests (prop_companionEVsAreRoots epsilon))
  quickCheck (withMaxSuccess maxTests (prop_quadraticIsomorphism epsilon))
