# Scalar types

We use [`Rational`](https://hackage.haskell.org/package/base-4.14.1.0/docs/Data-Ratio.html) to represent numbers in the contract. As of this writing, tolerance (number of decimals needed to evaluate equality) is set to 30. 

For the smart contract, we require calculations which are highly precise and can handle very large numbers and can be reproduced exactly across different hardware. Using FLOPs (floating point operations) is not compatible with these requirements. We are not able to determine exactly how big or how precise our numbers need to be, so we cannot say that FLOPs allow for enough size and precision. We can say, however, that FLOPs are implemented slightly differently on different hardware and results may not be reproducible across different hardware. Additionally, FLOPs are not allowed to be used in Plutus on-chain code. These are the constraints which do not allow us to use `Double` to represent numbers in the smart contract.

