# Future work \label{section:future}

Research opportunities that were out of scope for the current document

## What is the general **delta in incentives** off ethereum via **no-multistep-atomic-transactions**?

As mentioned in \ref{section:flashmitigation}, there are no multi-step atomic transactions in Cardano. 

## Compare/contrast **transaction-ordering dependence** risks across ethereum to cardano and other blockchains.

For the current document, we lack any confidence level regarding the frontrunning question because we are waiting on publications or code from IOHK to determine network fee resolution. A comment in [@CardanoNodeThroughput] suggests that miner-type frontrunning will not be an issue, but our confidence is not high in everything shaking out that way.

## Liquidity arbitrage

Liquidity arbitrage is when an arbitrageur attempts to play `Danaswap` pools against eachother. Liquidity tokens may be priced one way in subpool $P_i$ and priced another way in $P_j$. As an intuition, we can block this by making a different type of liquidity token per subpool, but we don't want to do this for user experience reasons. 

Arises due to parallelization. 

Liquidity arbitrage is when a arbitrageur attempts to play `Danaswap` pool sets against each other. When a pool has good utilization (i.e. is the right size), liquidity tokens via that pool will be 

for an arbitrary subpool, liquidity price is expressed in terms of a reference currency (stablecoin), it is a number that you'd have to pay of that reference stablecoin to buy one liquidity token _in that pool_. 

liquidity token price goes up with trading fees.

the fees divided by the dot product of prices and balances is the yield you have expressed in assets.

the relative increase of lt price (delta in assets / total assets). 

if i want to sell liquidity tokens i want to sell it where the price is highest, vice versa for lowest. 

**lt price is a cumulative metric for the amount of trading** in one subpool.

subpool Pi has lti, subpool Pj as ltj. we artificially price lti = ltj, opening ourselves up to two types of trouble. 

does depositing in a crappy subpool improve that subpool? 



For pools $P_i$ and $P_j$, 

## Ideal `Danaswap` vs. an attacker with infinite money \label{section:infinite}

We take the limit case of an idealized `Danaswap` which has arbitrary facility to add subpools and consider how an attacker with infinite money would approach `Danaswap`'s beliefs less true. This thought experiment could provide confidence in beliefs along the lines of \ref{section:pump}, and instruct us to for instance impose minimum trade requirements or implement automatic addition and subtraction of pools such that the protocol becomes more resilient to "economic DoS".

## Resilience of `Danaswap` to action-based \nameref{dfn:pump}

In \ref{section:pump} we considered trade-based manipulation and briefly mentioned centralization's opening to information-based manipulation, but [@Manipulation] also defines action-based manipulation. As Ardana is one component in a chaotic system consisting of many different kinds of agents and assets both onchain and offchain, there is _some_ degree to which action-based (like when you short-sell your own stock, close down your physical capital centers, cover your short position, then reopen the physical capital centers) manipulation could play a role. 
