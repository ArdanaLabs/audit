# Flashloans \label{section:flash}

Flashloans are associated with something like [`$136M`](https://peckshield.medium.com/bzx-hack-full-disclosure-with-detailed-profit-analysis-e6b1fa9b18fc) [in](https://news.bitcoin.com/defi-protocol-harvest-finance-hacked-for-24-million-attacker-returns-2-5-million/) [losses](https://www.coindesk.com/markets/2021/05/20/flash-loan-attack-causes-defi-token-bunny-to-crash-over-95/). 
\begin{definition}[Flashloan attack]\label{dfn:flashattack}
Let a \textbf{flashloan} be some multi-step transaction that begins with an uncollateralized loan and ends with repayment of that loan, with arbitrary logic in between. Then, a \textbf{flashloan attack} is some method of manipulating prices during such a transaction and profiting.
\end{definition}

Ethereum offers flash loans because they have **multi-step atomic transactions**. There is no such mechanism in Cardano. 

\begin{belief}[No flashloans]\label{blf:flash}
Flashloans will not be entering the Cardano ecosystem. 
\end{belief}

As such, 'Danaswap', Ardana stablecoins, and mechanisms related to `DANA` governance tokens are not vulnerable to flashloan attacks. 

## Action: monitoring Cardano for developments in multistep atomic transactions \label{section:flashmitigation}
Project Ardana will be monitoring the evolution of Cardano, because we believe that if multistep atomic transactions are introduced flashloans will be shortly around the corner.

### In this event,  the following mitigation strategy sketches will become urgent
* Onchain code only allow interop from one platform and users, not arbitrary platform.

* Lending products ought to require to collateralize in one whole transaction ahead of time before.

* Block price manipulation by disallowing mid-transaction information from updating prices.
