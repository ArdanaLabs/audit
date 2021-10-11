\chapter{Executive summary}

Platonic.Systems has conducted an internal \nameref{dfn:audit} parallel to the engineering efforts building Danaswap, Ardana stablecoins, and Dana governance token mechanisms. 

# Recommendations

Recommendations are assigned a five-valued confidence. 

## Keep the DeX closed source to prevent forking

This can play a role in reducing vampire attack risk. Confidence in importance: very low

## Peg fee structure to governance (i.e. `DANA` holders) to avoid competition 

This reduces vampire attack risk, details \ref{section:vampattacked}. Confidence in importance: medium. 

## Monitor development of Cardano ecosystem for **multi-step atomic transactions** to guard against flashloan attacks

With mitigation strategy sketches provided in \ref{section:flashmitigation}. Confidence in importance: very high

# Nonissues

During the audit process research was conducted to rule out the following attack vectors.

1. **Reentrancy**

2. **Flashloans** (modulo \ref{section:flashmitigation})


# Insufficient literature

As of this writing, the jury is still out on the following considerations or attack vectors.

1. **Transaction-ordering dependence**: waiting on publications or code from IOHK to determine network fee resolution and their impact on miner incentives. (This is blocking any confidence level regarding the frontrunning question). A comment in [@CardanoNodeThroughput] suggests that miner-type frontrunning will not be an issue, but our confidence is not high in everything shaking out that way. 

2. Filler, need a second item to block a render bug. 

