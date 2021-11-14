# A whale buys a high volume of `DANA` when the float is exhausted, forcing the protocol to buy it back at an arbitrary price

_This subchapter was cowritten with Bassam Awad_

An attack vector was internally raised and it led to some changes (\ref{section:diversify}) in the management of the protocol. For the current document to discuss it, we will provide some detail about Ardana's **pegging strategy** and consequences of `DANA`'s **deflationary** disposition. 

\begin{definition}[Pegging strategy]\label{dfn:pegging}
A mechanism that monitors and somehow "controls" or guides the price of an asset is a \textbf{pegging strategy} when it's intent is to keep the asset's price within a tight $\epsilon$ of some (stable) reference currency. 
\end{definition}

\begin{definition}[Float]\label{dfn:float}
We will call a pegging strategy that consists of maintaining a sum of assets (such as \texttt{DANA}) intended for buying and selling at time and volume such that a targeted stablecoin asset's (say \texttt{dUSD}'s) price can be guided to within $\epsilon$ of it's reference currency (say, \texttt{USD}) a \textbf{floating strategy}. Such a sum of assets is called a \textbf{float}, the term borrowed from in i.e. a coffee shop the sum of cash in the cash register for daily operation.
\end{definition}

Ardana **must** use a floating strategy because `DANA` is _deflationary_, or subject to no ad-hoc minting. This is discussed further below. Consequently, there is a question of **how much wealth should be tied up in the float**.

## Scenario: `DANA`'s price gets really high **and** the float is low at the same time

Consider the case when the float consists strictly of a `DANA` balance. Recall that the stablecoin protocol is **obliged** by the logic of it's smart contract to buy and sell stablecoins (like `dUSD`). We will see that **if the float consists only of `DANA`**, then the ability to do this is massively impacted by the price of `DANA`. 

1. Balance of the float dips under some threshold $\theta$. 

2. Some **whale** (agent with lots of capital) buys up a massive `DANA` position. 

3. To fulfill the pegging strategy, the Ardana stablecoin protocol is obliged to keep it's float above $\theta$. 

4. The whale can charge the protocol whatever it likes for `DANA`. 

This scenario is not just a problem for the protocol, but a \nameref{dfn:community} problem because **there's no guarantee that the protocol is liquid enough to fulfill it's obligations**. Thus, this scenario weakens the very notion of what a stablecoin is: an asset who's value is pegged to a reference asset. 

### Mitigation: diversify \label{section:diversify}

Because of the above exploit, Ardana has decided to diversify the float, introducing `ADA` to it. An **administrator** is now required to manually decide what asset the floating strategy operates in from time to time. Additionally, the float will be maintained as a **war chest**, and act as an investment fund during peacetime. Furthermore, debt auctions (see [@ArdanaWhitepaper]) will be allowed to use `ADA` instead of `DANA`. 

## Analysis \label{section:danagoupanalysis}

### Other protocols
One approach to this problem is asking the reasonable question _why doesn't MakerDAO [@MakerDAO] have this problem_? However, the answer (MakerDAO's pegging strategy is to mint and burn `MKR` as needed whereas `DANA` supply is fixed/deflationary) is too straightforward to be of any help. 

Curve's governance token `CRV` is on an inflation schedule, so while it's not deflationary like `DANA` it's not ad-hoc like `MKR`. In the case of this attack vector, we think `CRV` is closer to `DANA` than to `MKR`, so we are obliged to consider why hasn't Curve been subject to this attack? While an analysis of Curve's pegging strategy is out of scope for the current document, we weakly believe that this is something that simply hasn't happened _yet_ but there's no in-principle reason why Curve is resilient to this attack. 

### Best we can do

\begin{belief}[No float exploit mitigation strategy better than centralization]\label{blf:nofloatmitigation}
Obliging an administrative war chest to secure the protocol by diversifying the float is the best idea we have to mitigate the above scenario.
\end{belief}

### Centralization

The authorship of the current document is assured that it is Ardana's intentions to decentralize this mechanism as quickly as possible after launch. 
