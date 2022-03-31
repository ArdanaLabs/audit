# Scalar types

## `Danaswap`

The Ardana team uses [`PlutusTx.Rational`](https://github.com/input-output-hk/plutus/blob/master/plutus-tx/src/PlutusTx/Ratio.hs) to represent numbers in the `Danaswap` contract. As of this writing, tolerance (i.e., the number of decimal places needed to evaluate equality) is set to `20`. 

\begin{belief}[FLOPs incompatible with \texttt{Danaswap} requirements]\label{blf:noflop}
The `Danaswap` smart contract requires 1. extreme precision, 2. very large numbers, and 3. exact reproduction across varying hardware. Floating point operations (FLOPs) are incompatible with the requirements. 
\end{belief}

Addtionally, the `Danaswap` team does not know _a priori_ exactly how big the numbers need to be. Also, the `Floating` typeclass is not provided by `Plutus`, meaning if `Double` was used somewhere in the `Danaswap` codebase, it would have to be cast to `PlutusTx.Rational` at some point anyway. 

## The stablecoin

The stablecoin codebase also uses `PlutusTx.Rational` for ultimately similar reasons. 

## `DanaswapStats` 

`DanaswapStats` uses vanilla Haskell's `Double` type to log data about activities on `Danaswap`. 
