# Price manipulation \label{section:pump}

\begin{definition}[Truthfulness of a protocol's beliefs]\label{dfn:truebeliefs}
A protocol $\Pi$ beliefs are \textbf{true} when it's prices are accurate.
\end{definition}

\begin{definition}[Ideal exchange protocol]\label{dfn:idealprotocol}
An \textbf{ideal} exchange protocol is one who's beliefs are true.
\end{definition}

\begin{definition}[Arbitrage]\label{dfn:arbitrage}
When an agent can distinguish any given exchange protocol from an ideal protocol, they can profit by buying underpriced assets and selling overpriced assets. Such an agent is called an \textbf{arbitrageur}; we say that they are \textbf{doing arbitrage} or \textbf{exploiting} an arbitrage opportunity. 
\end{definition}

\begin{definition}[Price manipulation]\label{dfn:pump}
Given an exchange protocol $\Pi$, an attacker \textbf{manipulates prices} when they make $\Pi$'s beliefs less true. 
\end{definition}

\nameref{dfn:pump} can be thought of as the **imposition** of arbitrage opportunities. For many protocols, this is a serious attack vector. (TODO: CITATION). 

## Trade-base manipulation

\ref{dfn:pump} roughly corresponds to "market manipulation" found in [@Manipulation], which further defines a taxonomy of which here we consider the trade-based flavor. In trade-based manipulation, 
> the manipulator buys or sells in quantity, knowing that due to asymmetric information and trade processing and inventory costs prices will move in the direction of their trades [@Manipulation, p 5].

Trade-based manipulation in defi is most famously carried out with the help of \nameref{section:flash}, and as we claim in \ref{blf:flash} this is not a vector of attack. Another form trade-based manipulation could, in principle, take is if exchange $\Pi$ was already infected with false beliefs an agent $A$ could swap a high volume of asset $\$_i$ into asset $\$_j$ at $\Pi$ then go over to $\Theta$ with a high volume of asset $\$_j$ swapping it for $\$_i$, skewing $\Theta$'s beliefs about relative supply and demand of $\$_i$ and $\$_j$. It seems like $A$ would net a profit by playing $\Pi$ and $\Theta$ against eachother. However, we will argue that this is not a concern. 

\begin{belief}[No rational price trade-based manipulation]\label{blf:pricemanip}
Trade-base price manipulation on \texttt{Danaswap} costs more than it's worth
\end{belief}

The reasons for \ref{blf:pricemanip} are twofold: 

### 1. Invariant-driven beliefs

The prices of assets in `Danaswap` are driven by **the invariant equation** a la [@StableSwapWhitepaper], seeing also [@DanaswapWhitepaper] for details. If "value" $V$ is a reasonably well-behaved (i.e. something like "continuous") map from the set of assets to $\mathbb{R}$, then a price manipulation attack would be some way of siphoning out $\Sigma_{i = 1}^{n} V(\$_i)$ into the pocket of an attacker. It is the case that, due to transition system semantics and the invariant equation, any starting state $(x : \$_i, y: \$_j)$ **must** by construction transition to $(x - \delta : \$_i, y + \delta : \$_j)$ under the suitable swapping transaction; i.e. _must not_ transition to $(x - \delta : \$_i, y : \$_j)$ with the amount $\delta$ of $\$_i$ deposited into hte pocket of the attacker, by construction. 

There are two intuition pumps you can use to sympathize with this argument. 
1. There is a sort of _conservation law_ point of view, the statement $I(x) = 0$ from [@DanaswapWhitepaper] can be interpreted as saying "balances of assets are conserved" across the exchange. 
2. We observe an absence of prince manipulation scandals in Curve, the exchange based on [@StableSwapWhitepaper]. 

### 2. Incentive alignment

\begin{belief}[Arbitrage makes belief more true]\label{blf}
Arbitrageurs make \texttt{Danaswap}'s beliefs more true.
\end{belief}

In light of rudimentary definitions of arbitrage ([Wikipedia](https://en.wikipedia.org/wiki/Arbitrage#Price_convergence), [Investopedia](https://www.investopedia.com/terms/a/arbitrage.asp)), this is equivalent to believing that `Danaswap` forms a market at all. 

## Information-based manipulation

Another flavor in [@Manipulation]'s taxonomy is information-based manipulation. In information-based manipulation, the manipulator leverages **disinformation** to knock prices in a direction favorable to them [@Manipulation, p. 4]. 







DRAFT: 
you want to extract value from the system by making trades
1. trade in one direction to drive the exchange rate low in one direction, then buy back in the other direction. 
2. **assuming** a sufficient community (wait this isn't going anywhere)
3. the only way to extract money from a system is to bring the system closer to equilibrium, where eqilibrium is the V(a) = V(b). 



a huge trade will skew the exchange rates

anything that someone does will be evened out by the community of arbitrageurs, who will profit from fixing the situation.

