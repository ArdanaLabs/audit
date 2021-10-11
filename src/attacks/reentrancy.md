# Reentrancy

A procedure is **reentrant** if it can be initiated while it's already running or a prior initiation has been interrupted and both runs can terminate, failing to raise an error. The infamous "DAO Hack" of 2016 occurred because Solidity allows the programmer to write reentrant smart contracts [@SCSec, pp. 59-63]. 

\begin{belief}[No reentrancy]\label{blf:reent}
Plutus does not afford the freedom to write reentrant contracts.
\end{belief}

We can make a blanket statement that smart contracts in Cardano are invulnerable by construction to reentrancy. This is true because no transaction can be validated by (and it follows can require validation from) two different contracts. If you imagine Alice writes contract $A$ and invokes it (executing the program $\texttt{Alice}_A$) to validate transaction $T$, then Bob invokes $A$ ($\texttt{Bob}_A$) before Alice's invocation terminates, $T$ will be validated by **at most** one of $\texttt{Alice}_A$, $\texttt{Bob}_A$. 

As such, reentrancy attacks are not a threat to Danaswap, Ardana stablecoins, or any mechanism relating to Dana governance tokens. 
