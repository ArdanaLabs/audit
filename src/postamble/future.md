# Future work \label{section:future}

Numerous research opportunities are out of scope for the current document.

## What is the general **delta in incentives** off ethereum via **no-multistep-atomic-transactions**?

As mentioned in \ref{section:flashmitigation}, there are no multi-step atomic transactions in Cardano. 

## Compare/contrast **transaction-ordering dependence** risks across ethereum to cardano and other blockchains.

For the current document, we lack any confidence level regarding the frontrunning question because we are waiting on publications or code from IOHK to determine network fee resolution. A comment in [@CardanoNodeThroughput] suggests that miner-type frontrunning will not be an issue, but our confidence is not high in everything shaking out that way.

## Liquidity arbitrage

Liquidity arbitrage is when an arbitrageur attempts to play `Danaswap` pools against eachother. Liquidity tokens may be priced one way in subpool $P_i$ and priced another way in $P_j$. As an intuition, we can block this by making a different type of liquidity token per subpool; but we don't want to do this for user experience reasons (a zoo of liquidity tokens may be prohibitively difficult to reason about for all but a select few power users). 

There is also the extent to which liquidity arbitrage arises due to parallelization, with synchronization questions across pools complexifying the problem. 

Further research pressure ought to be applied to see if liquidity arbitrage aligns with the function of arbitrage in general (\ref{blf:arbtrue}) or forms a kind of threat. 

## Idealized `Danaswap` vs. an attacker with infinite money \label{section:infinite}

We take the limit case of an idealized `Danaswap` which has arbitrary facility to add subpools and consider how an attacker with infinite money would approach making `Danaswap`'s beliefs less true. This thought experiment could provide confidence in beliefs along the lines of \ref{section:pump}, and instruct us to for instance impose minimum trade requirements or implement automatic addition and subtraction of pools such that the protocol becomes more resilient to "economic DoS".

## Resilience of `Danaswap` to action-based \nameref{dfn:pump}

In \ref{section:pump} we considered trade-based manipulation and briefly mentioned centralization's opening to information-based manipulation, but [@Manipulation] also defines action-based manipulation. As Ardana is one component in a chaotic system consisting of many different kinds of agents and assets both onchain and offchain, there is _some_ degree to which action-based (like when you short-sell your own stock, close down your physical capital centers, cover your short position, then reopen the physical capital centers) manipulation could play a role. 

## Understand \ref{section:diversify} better to come up with a _minimal_ intervention

Ardana's intervention to mitigate the problem of a whale sitting on `DANA` is a little heavy handed. While it is in scope for the post-launch evolution of the platform to work on decentralizing the mitigation is installed at launch, it also may warrant application of research pressure to come up with different solutions. 

## Compare/contrast across the marketplace of throughput strategies

[@Throughput] seeds a methodology for analyzing throughput strategies, which should be built on as each new product introduces novel solutions. An example approach is for each product to answer the \nameref{section:frontrunning} question separately. 
