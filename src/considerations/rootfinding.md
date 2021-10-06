# Rootfinding

Recall the **invariant equation** from the StableSwap Whitepaper [@StableSwapWhitepaper, p. 5]. In the formalism provided by our Danaswap Whitepaper [@DanaswapWhitepaper, p. 6], there exists a function $I : S \rightarrow \mathbb{R}$ for contract states $S$ such that $I(s) = 0$ is equivalent to the invariant equation. 



In Curve's implementation of StableSwap, they use Newton's Algorithm [@NewtonAlg], so that's the first iteration of our codebase.

$$\begin{aligned}
    x^2 & = y + 1 \\
    \sqrt{} &\ \sqrt{} \\
    \midrule
    x & = \sqrt{y + 1}
\end{aligned}$$
