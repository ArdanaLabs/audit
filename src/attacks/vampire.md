\chapter{Attacks}

# Vampire attack

\begin{definition}[Vampire attack]\label{dfn:vampire}
Let $\Pi$ and $\Pi'$ be similar protocols, but $\Pi$ launched and attracted investors and customers earlier, and $\Pi'$ is somehow derivative of $\Pi$. Suppose $\Pi'$ competes with $\Pi$ such that $\Pi'$ makes parameter choices or other measures to become more attractive to investors or customers than $\Pi$. A $\textbf{vampire attack}$ is defined as the migration of value (liquidity or other assets) out of $\Pi$ into $\Pi'$.
\end{definition}

## The literature
Consult a selection of stories about vampire attacks. 

* [$\Pi' = \texttt{SushiSwap}$; $\Pi = \texttt{UniSwap}$](https://youtu.be/UFjXwrCGuog). SushiSwap was in fact a fork of UniSwap's code, and they provided incentives that directly targeted UniSwap investors and liquidity providers. This is the canonical notion of a vampire attack, with what appears to be the most written about it because of it's scale of impact and how early on the DeFi scene it was found. Our present definition is generalized for analysis that applies outside of the specific conditions here.

* [$\Pi' = \texttt{Swerve}$; $\Pi = \texttt{Curve}$](https://finance.yahoo.com/news/swerve-finance-total-value-locked-075020390.html). The term "vampire" does not occur in this article, but [blaize.tech](https://blaize.tech/services/how-to-prevent-liquidity-vampire-attacks-in-defi/) considers it to be a vampire attack. By forking Curve, Swerve offered a platform very similar to Curve's, and became competitive in TVL in a matter of days while people pulled out of Curve. There doesn't appear to be anything unique about Curve and Swerve being stablecoin DeXes. 

* [$\Pi' = \texttt{Artion}$; $\Pi = \texttt{Opensea}$](https://www.coindesk.com/tech/2021/09/24/andre-cronjes-new-nft-marketplace-is-a-vampire-attack-suicide-pact/). At current writing it's too early to tell, but it's possible that Artion by providing a platform competitive with Opensea will be considered to have vampire attacked it. Unfolding events for this to be the case would have to be that Artion is successful at the expense of Opensea. My choice to be influenced by a CoinDesk writer's choice to call this a vampire attack is up for debate, but my intention is to be consistent with the ecosystem and the literature and I don't see grounds to exclude this writer from either.

* [Extended notes on forks](https://newsletter.banklesshq.com/p/fork-defense-strategies-in-defi). 

### Major takeaways

* Lack of vampire attack stories in the Cardano ecosystem is, according to my analysis, not a by-construction property of Cardano. I.e. it's a matter of time. 

* Forking a codebase is often used as evidence in favor of the accusation that a given $\Pi'$ conducted a vampire attack, though forking is not an intrinsic property of the attack. 

## Scenario: reputational damage if we're considered $\Pi'$

Are there competing DeXs that beat us to market that could accuse us of vampire attacking them? Imagine if a bunch of Curve investors pull out their liquidity, exchange it for `ADA` on Coinbase, and start playing Danaswap. Would Curve think of that like a vampire attack?

## Scenario: value siphoned out if we become $\Pi$ \label{section:vampattacked}

Suppose another DeX for stablecoins launches with an incentive structure more attractive to our commmunity than our own.

Suppose further that, having open sourced the DeX contract code, this competitor copies our onchain code, and makes offchain code similar to ours themselves.

### Mitigations

* Keeping the DeX code closed source. This is a minor payout in risk reduction

* Peg fee parameters to democracy via governance token holders (so we don't have to worry about the wants and needs of the community not being met, we don't have to worry about competitors siphoning them away from us).

## Conclusion 

In any kind of market, participants take on the unavoidable risk of competitors showing up with better rates. The factor of code forking presented by the open source software context doesn't change this much, and the factor of parameters like fees presented by the economics of DeFi context doesn't either.
