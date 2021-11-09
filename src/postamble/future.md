# Future work \label{section:future}

Research opportunities that were out of scope for the current document

## What is the general **delta in incentives** off ethereum via **no-multistep-atomic-transactions**?

As mentioned in \ref{section:flashmitigation}, there are no multi-step atomic transactions in Cardano. 

## Compare/contrast **transaction-ordering dependence** risks across ethereum to cardano and other blockchains.

For the current document, we lack any confidence level regarding the frontrunning question because we are waiting on publications or code from IOHK to determine network fee resolution. A comment in [@CardanoNodeThroughput] suggests that miner-type frontrunning will not be an issue, but our confidence is not high in everything shaking out that way.

## Liquidity arbitrage

Liquidity arbitrage is when an arbitrageur attempts to play `Danaswap` pools against eachother. Liquidity tokens may be priced one way in subpool $P_i$ and priced another way in $P_j$. As an intuition, we can block this by making a different type of liquidity token per subpool, but we don't want to do this for user experience reasons. 

## Ideal `Danaswap` vs. an attacker with infinite money \label{section:infinite}

We take the limit case of an idealized `Danaswap` which has arbitrary facility to add subpools and consider how an attacker with infinite money would approach `Danaswap`'s beliefs less true. This thought experiment could provide confidence in beliefs along the lines of \ref{section:pump}, and instruct us to for instance impose minimum trade requirements or implement automatic addition and subtraction of pools such that the protocol becomes more resilient to "economic DoS".
