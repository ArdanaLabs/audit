# Price manipulation \label{section:pump}

\begin{definition}[Truthfulness of a protocol's beliefs]\label{dfn:truebeliefs}
A protocol $\Pi$'s beliefs are \textbf{true} when its prices are accurate.
\end{definition}

\begin{definition}[Ideal exchange protocol]\label{dfn:idealprotocol}
An \textbf{ideal} exchange protocol is one whose beliefs are true.
\end{definition}

\begin{definition}[Arbitrage]\label{dfn:arbitrage}
When an agent can distinguish any given exchange protocol from an ideal protocol, they can profit by buying underpriced assets and selling overpriced assets. Such an agent is called an \textbf{arbitrageur}; we say that they are \textbf{doing arbitrage} or \textbf{exploiting} an arbitrage opportunity. 
\end{definition}

\begin{definition}[Price manipulation]\label{dfn:pump}
Given an exchange protocol $\Pi$, an attacker \textbf{manipulates prices} when they make $\Pi$'s beliefs less true. 
\end{definition}

\nameref{dfn:pump} can be thought of as the **imposition** of arbitrage opportunities. For many protocols, this is a serious attack vector (see the [bZx](https://bzx.network/) margin trade feature for an example [](https://blog.peckshield.com/2020/02/15/bZx/)). 

## Trade-base manipulation

\ref{dfn:pump} roughly corresponds to "market manipulation" found in [@Manipulation], which further defines a taxonomy of which here we consider the trade-based flavor. In trade-based manipulation, 

> The manipulator buys or sells in quantity, knowing that due to asymmetric information and trade processing and inventory costs prices will move in the direction of their trades [@Manipulation, p 5].

Trade-based manipulation in defi is most famously carried out with the help of \nameref{section:flash}, and as we claim in \ref{blf:flash} this is not a vector of attack that concerns us. Another form trade-based manipulation could, in principle, take is if exchange $\Pi$ was already infected with false beliefs an agent $A$ could swap a high volume of asset $\$_i$ into asset $\$_j$ at $\Pi$ then go over to exchange $\Theta$ with a high volume of asset $\$_j$ swapping it for $\$_i$, skewing $\Theta$'s beliefs about relative supply and demand of $\$_i$ and $\$_j$. It seems like $A$ would net a profit by playing $\Pi$ and $\Theta$ against eachother in this way. However, we will argue that this is not a concern for the `Danaswap` exchange. 

\begin{belief}[No rational trade-based price manipulation]\label{blf:pricemanip}
Trade-base price manipulation on \texttt{Danaswap} costs more than it's worth
\end{belief}

The reasons for \ref{blf:pricemanip} are twofold: 

### Invariant-driven beliefs

The prices of assets in `Danaswap` are driven by **the invariant equation** a la [@StableSwapWhitepaper], seeing also [@DanaswapWhitepaper] for details. If "value" $V$ is a reasonably well-behaved (i.e. something like "continuous") map from the set of assets to $\mathbb{R}$, then a price manipulation attack would be some way of siphoning out $\Sigma_{i = 1}^{n} V(\$_i)$ into the pocket of an attacker. It is the case that, due to transition system semantics and the invariant equation, any starting state $(x : \$_i, y: \$_j)$ **must** by construction transition to $(x - \delta : \$_i, y + \delta : \$_j)$ under the suitable swapping transaction; i.e. _must not_ transition to $(x - \delta : \$_i, y : \$_j)$ with the amount $\delta$ of $\$_i$ deposited into the pocket of the attacker, by construction. 

There are two intuition pumps you can use to sympathize with this argument. 

1. There is a sort of _conservation law_ point of view, the statement $I(x) = 0$ from [@DanaswapWhitepaper] can be interpreted as saying "balances of assets are conserved" across the exchange. 

2. We observe an absence of prince manipulation scandals in Curve, the exchange based on [@StableSwapWhitepaper]. 

### Incentive alignment

\begin{belief}[Arbitrage makes belief more true]\label{blf:arbtrue}
Arbitrageurs make \texttt{Danaswap}'s beliefs more true.
\end{belief}

In light of rudimentary definitions of arbitrage ([Wikipedia](https://en.wikipedia.org/wiki/Arbitrage#Price_convergence), [Investopedia](https://www.investopedia.com/terms/a/arbitrage.asp)), this is trivially equivalent to believing that `Danaswap` forms a market at all. Consequently, if some agent puts pressure on making `Danaswap`'s beliefs less true, the community of arbitrageurs will step in and apply counterpressure because it is in their interest to do so, following the definition of arbitrage. 

## Information-based manipulation

Another flavor in [@Manipulation]'s taxonomy is information-based manipulation. In information-based manipulation, the manipulator leverages **disinformation** to knock prices in a direction favorable to them [@Manipulation, p. 4]. This attack vector is rather broad, we provide just two scenarios but one can readily imagine more. 

### Scenario: a false partnership 
Alice has a large `DANA` position. She compromises the account of a discord mod of a non-Ardana ecosystem product $\Pi$ and announces a new partnership between that product and Ardana. Since the false announcement came directly from a $\Pi$ discord mod, the $\Pi$ community believes it is true and there is a frenzy for `DANA`, driving up the price. 

#### A false partnership: branch one 
Influx of $\Pi$ community investors changes the balance of an upcoming governance decision.

#### A false partnership: branch two
When the hack is discovered it's a PR problem for Ardana. A redditor speculates that Alice is an Ardana insider, gaining a significant portion of the subreddit's total upvote volume that week.

### Scenario: shorting
At some point, there exists a protocol $\Phi$ that empowers speculators of Cardano to take short positions on Cardano-native tokens, perhaps this taking the form of contracts that pay out if a particular asset isn't trading for a forecasted price on some exchange. Bob gains a large short position against `DANA`. If Bob's short position isn't looking good, Bob might reach out to a journalist and fabricate a story about being a former Ardana employee who is now whistleblowing about something. The story is published, and people pull out of `DANA`, driving the price down.

## Conclusion 

`Danaswap`, Ardana stablecoins, and any mechanism relating to the `DANA` governance token each seem more resilient to price manipulation than other defi projects. Trade-based price manipulation is a nonissue. There exist ecosystem activities that remain a plausible opening to information-based price manipulation, where their plausibility is a function of personal security norms (see [@PersonalSecurity]) and integrity norms not simply of the Ardana \nameref{dfn:community} but of the ambient defi space, especially the Cardano defi space.
