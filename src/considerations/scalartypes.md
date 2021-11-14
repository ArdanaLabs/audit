# Scalar types

## `Danaswap`

The Ardana team uses [`PlutusTx.Rational`](https://github.com/input-output-hk/plutus/blob/master/plutus-tx/src/PlutusTx/Ratio.hs) to represent numbers in the `Danaswap` contract. As of this writing, tolerance (number of decimals needed to evaluate equality) is set to `20`. 

\begin{belief}[FLOPs incompatible with `Danaswap` requirements]\label{blf:noflop}
The `Danaswap` smart contract requires 1. extreme precision, 2. very large numbers, and 3. exact reproduction across varying hardware. Floating point operations (FLOPs) are incompatible with the requirements. 
\end{belief}

Addtionally, the `Danaswap` team does not _a priori_ know exactly how big the numbers need to be. Additionally, the `Floating` typeclass is not provided by `plutus`, meaning if `Double` was used somewhere in the `Danaswap` codebase, it would have to be cast to `PlutusTx.Rational` at some point anyway. 

## The stablecoin

The stablecoin codebase also uses `PlutusTx.Rational`. 

## `DanaswapStats` 

`DanaswapStats` uses vanilla haskell's `Double` type to log data about activities on `Danaswap`. 
