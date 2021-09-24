
-- https://github.com/ArdanaLabs/audit/issues/4#issuecomment-926091254
-- https://en.wikipedia.org/wiki/Companion_matrix

identity :: Int -> [[Double]]
identity n = [
  (take k $ repeat 0) ++ [1] ++ (take (n - 1 - k) $ repeat 0) | k <- [0..n - 1]
  ]

-- n is the number of assets on the balance sheet.
-- a and b are coefficients in terms of balance sheet and amplification coefficient.
-- -- here for details https://github.com/ArdanaLabs/audit/blob/main/newton-robustness.ipynb
companion :: Int -> Double -> Double -> [[Double]]
companion n a b = [
  (take n $ repeat 0) ++ [- b],
  [1] ++ (take (n - 1) $ repeat 0) ++ [-a]] ++ (tail $ take n $ identity (n + 1))

-- plug companion n a b into a eigensolver to get roots of the invariant polynomial.
