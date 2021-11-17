# Throughput

For Cardano defi to happen, the ecosystem needs clever solutions to transaction scalability[](https://liberlion.medium.com/concurrency-in-the-eutxo-model-is-not-a-problem-but-a-challenge-db4b395a8eda)[](https://sundaeswap.finance/posts/concurrency-state-cardano). A motivating example invoked in [@Throughput] is that Visa processed an average of 1700 transactions per second in 2019 (p. 14); how Cardano could compete with this kind of volume of service is a natural question to ask. At this early stage of the ecosystem, dapp and contract designers will each provide novel solutions, prompting a research opportunity to study those solutions and determine which solutions have the most desirable properties and the least undesirable properties. `Danaswap`'s throughput scalability strategy is given completely in [@DanaswapParallelism]. In the current document, we scrutinize one desirable property and determine that it is not present in `Danaswap`'s strategy, then we analyze the defi classic known as frontrunning.

## "Fairness"

\begin{definition}[Fairness]\label{dfn:fairness}
An exchange protocol's concurrency solution is \textbf{fair} if when two people perform an action at the same time, that action is performed for the same price. 
\end{definition}

\begin{definition}[Fragmented]\label{dfn:fragmented}
A UTXO state model is \textbf{fragmented} when there is more than one state UTXO in play at a time. 
\end{definition}

\begin{definition}[Normalized]\label{dfn:normalized}
A UTXO state model is \textbf{normalized} when there is neither disagreement nor redundancy regarding the data stored by the collection of UTXOs.
\end{definition}

`Danaswap`'s UTXO state model is _fragmented_ and _normalized_, owing to the scalability solution described in [@DanaswapParallelism]. 

\begin{belief}[No fair, fragmented, and normalized]\label{blf:fair}
In a \textit{fragmented} and \textit{normalized} UTXO state model, the fairness guarantee is impossible.
\end{belief}

The only way to have a fairness guarantee would be for each pool to update each other, which isn't possible to do in one transaction. 

## Frontrunning \label{section:frontrunning}

Frontrunning describes two different phenomena in the defi literature. In contrast to frontrunning in [the traditional finance literature](https://www.investopedia.com/terms/f/frontrunning.asp), defi frontrunning is not about information and time, rather it is about competition that arises from the unique context of transaction-ordering dependence (that is, uncertainty over the starting state of a transaction implies uncertainty over the finishing state of a transaction if there are multiple transactions involving some shared store asking to be mined).

As most of the frontrunning literature comes from the Ethereum ecosystem, and as we failed to find a frontrunning literature for Cardano, we do not have rigorous beliefs. We instead have a future research opportunity that would begin with explaining whether or not frontrunning vectors observed in Ethereum are likely or possible to be observed on Cardano. 

\begin{definition}[Investor-type frontrunning]\label{dfn:investorfrontrunning}
Given suitable transaction processing incentives such that transaction originators can make themselves more or less attractive to miners, \textbf{investor-type frontrunning} is when investor $A$ submits a trade at fee $x$ and investor $B$ hears about this and submits a similar trade at fee $x + \theta$ such that miners prefer to validate $B$'s trade. Consequently, $B$ receives the price $A$ thought they were going to get, and $A$ can receive a less favorable price.
\end{definition}

\begin{definition}[Mempool]\label{dfn:mempool}
Given a blockchain protocol such that transactions are submitted for miners to assemble, the place transactions "go" while waiting to be mined is called a \textbf{mempool}. 
\end{definition}

\begin{definition}[Miner-type frontrunning]\label{dfn:minerfrontrunning}
If transactions are visible in the mempool before they are mined, and the order of transactions is entirely up to miner's discretion, then malicious miners are provided an opportunity to leverage transaction ordering to suit their interests. 
\end{definition}

A treatment of miner-type frontrunning is given in [@SCSec, p. 64] for the Ethereum context. 

We conclude that for both types of frontrunning, it is not yet time to conduct a proper forecast of if or how much we expect to see them. We expect IOHK to push code and/or a publication sometime after Ardana's launch that will make it possible to conduct this research. The reader might monitor [@CardanoNodeThroughput] for a pulse of the ongoing situation. In particular, 

> The Cardano mempool is designed to be "fair". Transactions are processed in a FIFO [first in, first out] order regardless or how much in fees they pay (the ledger spec does support a fee market, but cardano-node doesn't take this into account). [@CardanoNodeThroughput]

Suggests that investor-type frontrunning as described is a nonissue, yet some fee market is liable to be implemented, as

> If there is network congestion, the only objective way to decide who to allow through is to prioritize the transactions with the most financial value which is proxy-defined by how much in fees they are willing to pay for the transaction to go through. [@CardanoNodeThroughput]


