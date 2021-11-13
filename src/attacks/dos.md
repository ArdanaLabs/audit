# Denial-of-service

\begin{definition}[Denial-of-service (DoS)]\label{dfn:dos}
A \textbf{denial-of-service} or \textbf{DoS} attack is a class of disruption that prevents intended users from reaching a service, usually accomplished by flooding or congesting.
\end{definition}

\begin{belief}[No unique DoS]\label{blf:nouniquedos}
Ardana ecosystem components do not offer a \textbf{unique} \nameref{dfn:dos} vector.
\end{belief}

However, we think \nameref{dfn:community} ought to be made aware of _ambient_ vulnerabilities in the broader Plutus and Cardano ecosystem. 

## Onchain

We rely on [@MlabsSlab] to describe three flavors of onchain DoS vector, which essentially target `Validator`s or `Redeemer`s.

\begin{definition}[Token dust attack]\label{dfn:tokendust}
An attacker crams hundreds of unique tokens with different \texttt{CurrencySymbol}s/\texttt{TokenName}s into a single UTXO intending for it's representation to challenge the \texttt{16kb} limit. Then, the UTXO is placed in a \texttt{Validator} in such a way that one or more \texttt{Redeemer}s will need to consume it, blocking transactions on that \texttt{Validator}-\texttt{Redeemer} pair.
\end{definition}

\begin{definition}[Datum too big]\label{dfn:largedatum}
In the datum field, an attacker puts an unbounded data structure on a UTXO that happens to demand consumption by a \texttt{Redeemer} which is critical to honest users. 
\end{definition}

\begin{definition}[EUTXO concurrency DoS]\label{dfn:concurrencydos}
An attacker submits a barrage of vacuous transactions consuming blocking EUTXOs.
\end{definition}

[@MlabsSlab] points to [@NativeTokFAQ] section on `Min-Ada-Value` as a mechanism that can be leveraged to block \nameref{dfn:tokendust}, but it's on the developer to set it and its implementation effects honest users.

> Every output created by a transaction must include a minimum amount of `ADA`, which is calculated based on the size of the output (that is, the number of different token types in it, and the lengths of their names). [@NativeTokFAQ].

With similar drawbacks, fees or discincentives could block \nameref{dfn:concurrencydos}, where again honest users are impacted by the mechanism.

Neither ourselves nor [@MlabsSlab] provide a strategy against \nameref{dfn:largedatum}.

## Offchain \label{section:pabdos}

As of this writing, `plutus` depends on the JSON parsing and encoding library [`aeson`](https://hackage.haskell.org/package/aeson). This means that `PAB` artefacts, if the `aeson` version is `< 2.0.1.0`, will be subject to the known DoS vulnerability described in [@AesonDos]. 

### Recomendation

Build system should enforce `aeson >= 2.0.1.0`.

## Conclusion

\nameref{dfn:dos} vectors are currently a part of Cardano. With respect to these vectors, we do not believe Danaswap nor anything in the Ardana ecosystem is better or worse off (\ref{blf:nouniquedos}). 

