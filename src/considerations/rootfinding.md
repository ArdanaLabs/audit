# Rootfinding

`Danaswap` takes a novel root-finding strategy of the team's own devising. An in depth treatment will be in a future publication. In the current document's scope is a brief registration of of Ardana's belief that invariant-driven prices will behave desirably, which is to say the implementation will provide behavior that the formal model predicts. 

Recall the **invariant equation** from the StableSwap Whitepaper [@StableSwapWhitepaper, p. 5]. In the formalism provided by our Danaswap Whitepaper [@DanaswapWhitepaper, p. 3], there exists a function $I : S \rightarrow \mathbb{R}$ for contract states $S$ such that $I(s) = 0$ is equivalent to the invariant equation. Danaswap borrows everything from StableSwap to vary between constant-product and constant-sum market-making according to a _leverage_ parameter, for which we also accept the suggestion found in [@StableSwapWhitepaper]. We either hold all balances constant to solve for a number $D$, which has the semantics of total amount of coins _when_ all coins have equal price, or we hold $D$ and all but a given balance constant and solve for the given balance. Since this looks like solving an equation of some function set to zero, we call this "finding the roots" of a function or "solving for the function's zeros".

\begin{belief}[Exactly one positive real root of invariant functions]\label{blf:uniqueposreal}
Given $n + 1$ invariant functions, one for each of $n$ balances plus one for the constant $D$, each invariant function has exactly one positive real root. 
\end{belief}

In the upcoming publication, we will leverage the contents of a precalculus course in the US to justify this belief, include a derivation from [@StableSwapWhitepaper] to monic polynomials, and discuss Ardana's rootfinding algorithm with regard to other rootfinding methods in the literature or related ecosystems.

To be clear, if we did not have \ref{blf:uniqueposreal}, the invariant equation would either be ambiguous (a subjective choice of _which_ positive real root would be needed), or provide negative or complex balances making it effectively undefined. 

While Curve uses [Newton's method](https://en.wikipedia.org/wiki/Newton%27s_method) to get zeros of the invariant equation, `Danaswap` uses a home rolled algorithm that leverages \ref{blf:uniqueposreal} to provide arbitrary precision one hundred percent of the time.
