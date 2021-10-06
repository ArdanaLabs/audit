\chapter{Appendices}
# Appendix A: invariant polynomial

[@StableSwapWhitepaper] gives us a way of easing between constant-sum and constant-product market-making by a coefficient $\chi$ called _leverage_, which turns out to be a function of $D$ and $B(s)$, where $B : S \rightarrow \mathbb{R}^n$\footnote{Balances are strictly positive, so it's not really $\mathbb{R}^n$, however we enjoy some vector space properties in [@DanaswapWhitepaper, p. 6] so we do not constrain the set.} is a function assigning in every state a balance to each of $n$ assets. In what follows, let $x = B(s)$ such that $x_j = B(s)_j$ for each asset label $j$.

$$\chi D^{n-1} \Sigma x_i + \Pi x_i = \chi D^n + \left( \frac{D}{n} \right)^n$$

When $\chi$ is a blackbox, there is very little analysis available regarding the existence and behavior of roots or the convergence of any root-finding algorithm. We will forego any gains of abstracting over leverage coefficients, and let $\chi = \frac{A (\Pi x_i) n^n}{D^n}$ before proceeding. 

## Derivation of invariant polynomials

First we derive $I_D$, the polynomial in unknown $D$. 

\begin{derivation}
$$\begin{aligned}
\chi D^{n-1} \Sigma x_i + \Pi x_i & = \chi D^n + \left( \frac{D}{n} \right)^n \\
\midrule \\
\frac{A (\Pi x_i) n^n}{D^n} D^{n-1} \Sigma x_i + \Pi x_i & = \frac{A (\Pi x_i) n^n}{D^n} D^n + \left( \frac{D}{n} \right)^n \\
\midrule
\frac{A (\Pi x_i) n^n}{D} \Sigma x_i + \Pi x_i & = A (\Pi x_i) n^n + \frac{1}{n^n} D^n \\
\times D &\ \ \times D & \\
\midrule
A n^n (\Pi x_i) \Sigma x_i + (\Pi x_i) D & = A n^n (\Pi x_i) D + \frac{1}{n^n} D^{n+1} & \\ 
- A n^n (\Pi x_i) D - \frac{1}{n^n} D^{n+1} &\ \ - A n^n (\Pi x_i) D - \frac{1}{n^n} D^{n+1} \\
\midrule
A n^n (\Pi x_i) \Sigma x_i + (\Pi x_i) D - A n^n (\Pi x_i) D - \frac{1}{n^n} D^{n+1} & = 0 \\
\midrule
\frac{-1}{n^n} D^{n+1} + (1 - A n^n) (\Pi x_i) D + A n^n (\Pi x_i) \Sigma x_i & = 0 \\
\times - n^n &\ \ \times - n^n \\ 
\midrule
D^{n+1} - n^n (1 - A n^n) (\Pi x_i) D - A n^{2n} (\Pi x_i) \Sigma x_i & = 0 \\
\midrule 
D^{n+1} + (A - n^{-n}) n^{2n} (\Pi x_i) D + - A n^{2n} (\Pi x_i) \Sigma x_i & = 0 \\
\end{aligned}$$
\end{derivation}

We now have a polynomial in $x \mapsto x^{n+1} + a x + b$ form, for constants $a$ and $b$ which are functions of a balance sheet and the _amplification coefficient_ $A$. 

\begin{derivation}
$\forall k \in 1..n,$ 
$$\begin{aligned}
\frac{A (\Pi x_i) n^n}{D^n} D^{n-1} \Sigma x_i + \Pi x_i & = \frac{A (\Pi x_i) n^n}{D^n} D^n + \left( \frac{D}{n} \right)^n \\
\midrule
\frac{A n^n}{D} (\Pi_{i \neq k} x_i) x_k (x_1 + ... + x_k + ... + x_n) + (\Pi_{i \neq k} x_i) x_k & = A n^n (\Pi_{i \neq k} x_i) x_k + \frac{D^n}{n^n} \\
\midrule
\frac{A n^n}{D} (\Pi_{i \neq k} x_i) x_k^2 + \frac{A n^n}{D} (\Pi_{i \neq k} x_i) (\Sigma_{i \neq k} x_i) x_k + (\Pi_{i \neq k} x_i) x_k & = A n^n (\Pi_{i \neq k} x_i) x_k + \frac{D^n}{n^n} \\
- A n^n (\Pi_{i \neq k} x_i) x_k - \frac{D^n}{n^n} &\ \ - A n^n (\Pi_{i \neq k} x_i) x_k - \frac{D^n}{n^n} \\
\midrule
\frac{A n^n}{D} (\Pi_{i \neq k} x_i) x_k^2 + \left((\Pi_{i \neq k} x_i) \left( \frac{A n^n}{D} \Sigma_{i \neq k} x_i + 1 - A n^n \right) \right) x_k + \frac{- D^n}{n^n} & = 0 \\
\div \frac{A n^n}{D} (\Pi_{i \neq k} x_i) &\ \ \div \frac{A n^n}{D} (\Pi_{i \neq k} x_i) \\
\midrule
x_k^2 + \left( \Sigma_{i \neq k} x_i + \frac{D}{A n^n} - D \right) x_k + \frac{-D^{n+1}}{A n^{2n} \Pi_{i \neq k} x_i} & = 0 \\
\midrule
x_k^2 + \left( \Sigma_{i \neq k} x_i - D (1 - \frac{1}{A n^n})\right) x_k + \frac{-D^{n+1}}{A n^{2n} \Pi_{i \neq k} x_i} & = 0
\end{aligned}$$
\end{derivation}

## Analysis of roots and of derivatives

TODO
