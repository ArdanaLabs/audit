-- |

module Main where

import Companion.Types

import Test.Generators
import Test.Quadratic

import Test.QuickCheck

precisionOOM = 2
epsilon = 1 / 10 ^ precisionOOM

maxTests = 10000

main = do
  companionQuadraticNoComplex <- quickCheckResult (withMaxSuccess maxTests prop_companionQuadraticNoImaginary)
  companionQuadraticUniquePosrealRoot <- quickCheckResult (withMaxSuccess maxTests prop_companionQuadraticUniquePosrealRoot)
  formulaRootsAreRoots <- quickCheckResult (withMaxSuccess maxTests (prop_formulaRootsAreRoots epsilon))
  companionEVsAreRoots <- quickCheckResult (withMaxSuccess maxTests (prop_companionEVsAreRoots epsilon))
  quadraticIsomorphism <- quickCheckResult (withMaxSuccess maxTests (prop_quadraticIsomorphism epsilon))
  -- print companionQuadraticNoComplex
  -- print companionQuadraticUniquePosrealRoot
  -- print formulaRootsAreRoots
  -- print companionEVsAreRoots
  -- print quadraticIsomorphism
  return ()
