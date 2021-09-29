# Flashloans

Flashloans are associated with something like [`$136M`](https://peckshield.medium.com/bzx-hack-full-disclosure-with-detailed-profit-analysis-e6b1fa9b18fc) [in](https://news.bitcoin.com/defi-protocol-harvest-finance-hacked-for-24-million-attacker-returns-2-5-million/) [losses](https://www.coindesk.com/markets/2021/05/20/flash-loan-attack-causes-defi-token-bunny-to-crash-over-95/).

Ethereum offers flash loans because they have **multi-step atomic transactions**. Cardano does not have these. So in spite of [`Aada`](aada.finance)'s claims, we are not expecting flash loans to enter the Cardano ecosystem at this time. There may be lessons from the attacks in the reports, but they are not entirely straightforward. The question is: is there anything _unique_ introduced by the flash loan mechanism? The auditing research opportunity here is not a huge priority.

### Action: monitoring Cardano for developments in multistep atomic transactions
Project Ardana will be monitoring the evolution of Cardano, because we believe that if multistep atomic transactions are introduced flashloans will be shortly around the corner.

### In this event,  the following mitigation strategy sketches will become urgent
* Onchain code only allow interop from one platform and users, not arbitrary platform.

* Lending products ought to require to collateralize in one whole transaction ahead of time before.

* Block price manipulation by disallowing mid-transaction information from updating prices.

