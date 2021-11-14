# This is part of a previous draft of `src/considerations/rootfinding.md`


Recall the **invariant equation** from the StableSwap Whitepaper [@StableSwapWhitepaper, p. 5]. In the formalism provided by our Danaswap Whitepaper [@DanaswapWhitepaper, p. 3], there exists a function $I : S \rightarrow \mathbb{R}$ for contract states $S$ such that $I(s) = 0$ is equivalent to the invariant equation. Danaswap borrows everything from StableSwap to vary between constant-product and constant-sum market-making according to a _leverage_ parameter, for which we also accept the suggestion found in [@StableSwapWhitepaper]. Sometimes, we need to hold all balances constant to solve for $D$ (which we call _the invariant_, having the semantics of total amount of coins **when** all coins have equal price). Other times, we consider a $k$ and solve for $B(s)_k$ holding everything else (including $D$) constant, when $B : S \rightarrow \mathbb{R}^n$ is a function assigning in every state a balance to each of $n$ assets (we will think of an $i \in 1..n$ as an _asset label_). 

We define the **invariant polynomial** $n + 1$ times like so

\begin{definition}[Invariant polynomials]\label{dfn:invpolyn}
$$\begin{aligned}
    I_D & := D \mapsto D^{n+1} + (A + n^{-n})n^{2n}(\Pi B(s)_i) D + - A n^{2n} (\Pi B(s)_i) \Sigma B(s)_i \\
    \forall k \in 1..n, I_k & := B(s)_k \mapsto B(s)_k^2 + \left(\Sigma_{i \neq k} B(s)_i + (\frac{1}{A n^n} - 1) D \right) x_k + \frac{-D^{n+1}}{A n^{2n}\Pi_{i \neq k} B(s)_i}
\end{aligned}$$
\end{definition}

The derivations beginning with [@StableSwapWhitepaper] are attainable via an algebra education, but will be included in the aforementioned future publication. 

The derivations beginning with [@StableSwapWhitepaper] are in \nameref{apdx:inv} (\nameref{drvn:ID}, \nameref{drvn:Ik}).



We think the invariant equation is best represented as polynomials set to zero, depending on what you're solving for, for the following reasons

1. **Characterize the roots in terms of existence and uniqueness**. It can be shown that there is exactly one nonnegative real root for $I_D$ and each $I_k$, and we'd like the onchain code to be close to the form that makes this easy to see. 

## Newton's algorithm 

In Curve's implementation of StableSwap, they use Newton's algorithm for root finding, so that's the first iteration of our codebase.

When the derivative can be found in a neighborhood of zero, Newton's method does not enjoy convergence guarantees [@NewtonAlg, para. 4.1]. The probability that invariant polynomial derivatives are in such a neighborhood is tiny, but nonzero, with details in \ref{apdx:inv}. 

We currently solve in `DanaswapStats` and oblige onchain logic to provide an $\epsilon$-proof that the root is valid. 



