# Vampire attack

\begin{definition}[Vampire attack]\label{dfn:vampire}
Let $\Pi$ and $\Theta$ be similar protocols, but $\Pi$ launched and attracted investors and customers earlier, and $\Theta$ is somehow derivative of $\Pi$. Suppose $\Theta$ competes with $\Pi$ such that $\Theta$ makes parameter choices or other measures to become more attractive to investors or customers than $\Pi$. A $\textbf{vampire attack}$ is defined as the migration of value (liquidity or other assets) out of $\Pi$ into $\Theta$.
\end{definition}

## The literature
Consult a selection of stories about vampire attacks. 

* [$\Theta = \texttt{SushiSwap}$; $\Pi = \texttt{UniSwap}$](https://youtu.be/UFjXwrCGuog). SushiSwap was in fact a fork of UniSwap's code, and they provided incentives that directly targeted UniSwap investors and liquidity providers. This is the canonical notion of a vampire attack, with what appears to be the most written about it because of it's scale of impact and how early on the defi scene it was found. Our present definition is generalized for analysis that applies outside of the specific conditions here.

* [$\Theta = \texttt{Swerve}$; $\Pi = \texttt{Curve}$](https://finance.yahoo.com/news/swerve-finance-total-value-locked-075020390.html). The term "vampire" does not occur in this article, but [blaize.tech](https://blaize.tech/services/how-to-prevent-liquidity-vampire-attacks-in-defi/) considers it to be a vampire attack. By forking Curve, Swerve offered a platform very similar to Curve's, and became competitive in total value locked (TVL) in a matter of days while people pulled out of Curve. There doesn't appear to be anything unique about Curve and Swerve being stablecoin exchange protocols. 

* [$\Theta = \texttt{Artion}$; $\Pi = \texttt{Opensea}$](https://www.coindesk.com/tech/2021/09/24/andre-cronjes-new-nft-marketplace-is-a-vampire-attack-suicide-pact/). At current writing it's too early to tell, but it's possible that Artion by providing a platform competitive with Opensea will be considered to have vampire attacked it. Unfolding events for this to be the case would have to be that Artion is successful at the expense of Opensea. My choice to be influenced by a CoinDesk writer's choice to call this a vampire attack is up for debate, but my intention is to be consistent with the ecosystem and the literature and I don't see grounds to exclude this writer from either.

* See extended notes on forks in [@ForkDefense]. 

### Major takeaways

* Lack of vampire attack stories in the Cardano ecosystem is, according to my analysis, not a by-construction property of Cardano. I.e. it's a matter of time. 

* Forking a codebase is often used as evidence in favor of the accusation that a given $\Theta$ conducted a vampire attack, though forking is not an intrinsic property of the attack. 

## Scenario: reputational damage to Ardana if it is considered $\Theta$

If you imagine a competing exchange protocol beat Ardana to market, then in principle Ardana could be (weakly) accused of vampire attacking them. 

Imagine if a bunch of Curve investors pull out their liquidity, exchange it for `ADA` on Coinbase, and start playing `Danaswap`. Would Curve think of that like a vampire attack? The literature has not seen a vampire attack across a distance as great as that between Ethereum and Cardano, but that's only because it is early. 

If the literature or ecosystem chooses to view Ardana as a vampire attacker, the project could suffer reputational damage. However, even in this event, it needs to be shown that the public relations problem is actually significant. I.e., is $\Theta$'s public relations challenges impacted severely by a vampire attack accusation? It might warrant further research, but we do not conduct that research in the current document. 

## Scenario: value siphoned out if we become $\Pi$ \label{section:vampattacked}

Suppose another exchange protocol for stablecoins launches with an incentive structure more attractive to our \nameref{dfn:community} than our own. Then, everyone could choose to migrate to this other protocol. According to the literature, we would be justified in considering this a vampire attack. 

Suppose further that, having open sourced the `Danaswap` repo, this competitor's product is a fork of our own, making supplement components for any aspects that were closed source. If we follow the literature, we would be even more justified in considering this a vampire attack. 

### Mitigations

* **Keeping the `Danaswap` code closed source**. This is a minor payout in risk reduction. We can also make a custom license, make it source available but proprietary, etc. 

* **Peg fee parameters to democracy via `DANA` governance token holders**. The \nameref{dfn:community}'s preferences are a part of the competitive landscape; if a derivative competitor is closer to our \nameref{dfn:community}'s wants and needs than we are, then the Ardana \nameref{dfn:community} will be siphoned out of Ardana. An automatic mechanism to decrease this possibility would look simply like setting policies such as the fee structure with vote inputs from the \nameref{dfn:community}, however, automation shouldn't be the last word; attention and care will have to be paid to make sure people are actually using the mechanism. We see this having a stronger payout in risk reduction. 

## Conclusion 

In any kind of market, participants take on the unavoidable risk of competitors showing up with better rates. The factor of code forking presented by the open source software context doesn't change this much, and the factor of fee structure parameters presented by the cryptoeconomic context doesn't either.

Vampire attack is a loose mirage of competitive phenomena: ultimately judged by the ecosystem literature, often coming down to individual journalists or researchers. It is in principle possible to be accidentally accused of vampire attacking. We do not want value siphoned out: there exist some practices to decrease this possibility that mostly amount to community engagement and giving the community a real voice in the system.
