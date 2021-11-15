Platonic.Systems has conducted an internal \nameref{dfn:audit} parallel to the engineering efforts building `Danaswap`, Ardana stablecoins, and `DANA` governance token mechanisms. 

# Recommendations

Recommendations are assigned a five-valued confidence. 

## Keep Ardana components closed source, or under complex licensing, to prevent forking

This can play a role in reducing vampire attack risk. Confidence in importance: very low

## Peg fee structure to governance (i.e. `DANA` holders) to avoid competition 

This reduces vampire attack risk, details \ref{section:vampattacked}. Confidence in importance: medium. 

## Monitor development of Cardano ecosystem for **multi-step atomic transactions** to guard against flashloan attacks

With mitigation strategy sketches provided in \ref{section:flashmitigation}. Confidence in importance: very high

## Enforce `aeson >= 2.0.1.0` at build time.

\ref{section:pabdos}. Confidence in importance: very high. 

# Nonissues

During the audit process research was conducted to rule out the following attack vectors.

1. **Reentrancy**

2. **Flashloans** (modulo \ref{section:flashmitigation})

3. **Trade-based price manipulation**

# Insufficient literature

As of this writing, the jury is still out on the following considerations or attack vectors. Research opportunities are detailed in \ref{section:future}.

1. **Transaction-ordering dependence**: waiting on publications or code from IOHK to determine network fee resolution and their impact on miner incentives. 

2. **Cost semantics and gas**: waiting on publications or code from IOHK to determine network fee resolution. 

3. **Action-based price manipulation**: data that will be available post launch about Ardana utilization could inform research on this. 
