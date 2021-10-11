# Throughput

TODO: establish throughput problem with language from [@Throughput].

\begin{definition}[Fairness]\label{dfn:fairness}
A DeX's concurrency solution is \textbf{fair} if when two people perform an action at the same time, that action is performed for roughly the same price. 
\end{definition}

> The Cardano mempool is designed to be "fair". Transactions are processed in a FIFO order regardless or how much in fees they pay (the ledger spec does support a fee market, but cardano-node doesn't take this into account) [@CardanoNodeThroughput]

TODO: language to discuss this quote.

\begin{definition}[Fragmented]\label{dfn:fragmented}
A UTXO state model is \textbf{fragmented} when there is more than one state UTXO in play at a time. 
\end{definition}

\begin{definition}[Normalized]\label{dfn:normalized}
A UTXO state model is \textbf{normalized} when there is neither disagreement nor redundancy regarding the data stored by the collection of UTXOs.
\end{definition}

Our UTXO state model design is _fragmented_ yet _normalized_. In such a model, a fairness guarantee is impossible: to have a fairness guarantee, each pool would have to update eachother, which isn’t possible to do in one transaction. 
