# Flash loans

# Executive summary

Ethereum offers flash loans because they have **multi-step atomic transactions**. Cardano does not have these. So in spite of `Aada`'s claims, we are not expecting flash loans to enter the Cardano ecosystem at this time. There may be lessons from the attacks in the reports, but they are not entirely straightforward. The question is: is there anything _unique_ introduced by the flash loan mechanism?:w
The auditing research opportunity here is not a huge priority.

## Takeaway that definitely goes into the audit
Project Ardana will be monitoring the Cardano ecosystem's evolution **very** closely to check if they're thinking about introducing multistep atomic transactions. 

#### In the event of this happening, the following mitigation strategy sketches will become rather urgent. 
- Onchain code only allow interop from one platform and users, not arbitrary platform
- Lending products ought to require to collateralize in one whole transaction ahead of time before.
- Block price manipulation by disallowing mid-transaction information from updating prices

# Long report - [Attacks](#Attacks) - [Mitigation](#Mitigation) - [Summary](#Summary)

Ardana does not offer flash loans directly. 

However, **what are the consequences of another platform on Cardano offering flash loans?** [`aada.finance`](aada.finance) ([whitepaper](https://aada.finance/whitepaper/aada_white_paper_V1.1.pdf)) will offer this. There are currently no plans for any lowcode/nocode offerings, but flash loans will be available to developers. I found no timeline information on their website (I can send cold messages on linkedin to see if they're willing to divulge this information, if we think expected arrival date of flash loans is valuable information).

### What is a flash loan? 

A flash loan, in ethereum, is a **multi-step transaction** that begins with an uncollateralized loan (or has uncollateralized lending near the beginning) and ends with that loan being repayed (or has repayment near the end). Steps in the middle are arbitrary (bounded in length by the max gas cost of a transaction): they can interact with arbitrary platforms or services. So for example, if AAVE provides the flash loan, intermediate steps in the loan can be interactions with UniSwap. Flash loans are considered one atomic transaction; not unlike `BEGIN; ... COMMIT` in SQL, every step will reverse/cancel if one step fails. 

## Use cases

According to finematics, the [three main investor opportunities discovered in ethereum upon the introduction of flash loans](https://youtu.be/mCJUhnXQ76s?t=371) are 
1. Collateral swap: Suppose you take out a collateralized loan. You can swap the collateral asset in a several-step flash loan by repaying the loan in the second step, swapping your returned collateral for a different asset in the third step, taking out a new loan with that new asset you got in the swap to in the fourth step repay the flash loan. 
2. Arbitrage: suppose there's a DAI-USDC pool in one DeX and a DAI-USDC pool in another. If you discover a price discrepancy between them, you can magnify your arbitrage profits by leveraging a flash loan. Here, the slippage question requires attention, especially if your `order size / liquidity available` ratio is high. You also have to worry about gas fees and frontrunning. 
3. Self liquidation: consider the liquidation condition in the MakerDAO protocol, in which a pool that is considered too risky is liquidated in auctions. Suppose your assets are nearing that threshold and are about to be liquidated by the protocol. 
> You can take a flash loan for the amount of DAI that you owe, repay your DAI loan and withdraw your ETH, swap enough ETH to DAI in order to repay the flash loan + fees, keep the rest of your ETH (- [source](https://finematics.com/flash-loans-explained/))

More use cases may be discovered. 

# Attacks

The six attacks I've found as of this draft sum to `$136.083M` in losses. (The price volatility of the assets in question make this a moving target, in all honesty). (Also "losses" means a few different things, price dives or siphoning or attacker gains).

## bZx - February 2020 - losses `$350k + $633k` (two distinct moments)

The steps in this attack are
1. flashloan borrow
2. hoard
3. margin pump
4. dump 
5. flashloan repay

The flashloan borrow is straightforward, the hoard step is a collateralized loan. So they flashloan borrowed 10k ETH and collateralized 5.5k of it to borrow 112 WBTC. The margin pump step is where things get intricate and creative. bZx has a "margin trade" feature which allows shorting, in this case the attacker shorted ETH to the favor of WBTC. The internals of the margin trade function calls out to KyberSwap, which in this case happened to land on it's KyberUniswap reserve. This drove the price of WBTC in Uniswap up 3x. Before the dump, there are no gains in the attacker's assets. In the dump, the attacker sells 112 WBTC to uniswap for WETH. The dump netted the attacker ~6871 ETH. Finally, they repay the flashloan. 

### [news](https://www.coindesk.com/tech/2020/02/19/everything-you-ever-wanted-to-know-about-the-defi-flash-loan-attack/) - [peckshield](https://blog.peckshield.com/2020/02/15/bZx/) ([medium version](https://peckshield.medium.com/bzx-hack-full-disclosure-with-detailed-profit-analysis-e6b1fa9b18fc))

## Harvest - October 2020 - losses `$24M`

Harvest is a [yield aggregator](https://docs.google.com/document/d/1dgKUET3Ngo-B_LPDXuqSJvAewe7IIKAxiWMSdVXD9q8/edit?usp=sharing).

> Harvest Finance revealed that the hacker “manipulated prices on one money lego (curve y pool) to drain another money lego [farm USDT (fUSDT), farm USDC (fUSDC)], many times. The attacker then converted the funds to renBTC and exited to bitcoin.”

Peckshield did not publically cover this one. I'm sparse on details.

### [news](https://news.bitcoin.com/defi-protocol-harvest-finance-hacked-for-24-million-attacker-returns-2-5-million/)

## Homora-Cream - February 2021 - losses `$37.5M`

[Alpha homora](homora.alphafinance.io) is a [yield farming](https://docs.google.com/document/d/1dgKUET3Ngo-B_LPDXuqSJvAewe7IIKAxiWMSdVXD9q8/edit?usp=sharing) service in "the alpha ecosystem". 

Cream was in some sense more of the victim here, but Alpha Homora was the site of the vulnerability.

I can't find a lot of details.

### [news](https://www.coindesk.com/markets/2021/02/13/defi-protocols-cream-finance-alpha-exploited-in-flash-loan-attack-375m-lost/)

## Pancake Bunny - May 2021 - losses `$45M` 

(an estimate that `>$200M` of value was destroyed, because the price dipped 95%).

Struggling to find an adequate breakdown. 

### [news](https://www.coindesk.com/markets/2021/05/20/flash-loan-attack-causes-defi-token-bunny-to-crash-over-95/) - [source two](https://medium.com/amber-group/bsc-flash-loan-attack-pancakebunny-3361b6d814fd)

## Bogged - May 2021 - losses `$3.6M`

> **While it appears to be a flashloan attack, it is a flashswap-assisted one.** [emph added]

This attack inflated a balance of the BOG token. 

> Step 1: Take nine flash-swaps and add liquidity into the WBNB+BOG pool. Each flash-swap leads to 47,770 BOG and the entire process consumes 88,159.43 WBNB with 83,440.57 LP token minted.

> Step 2: Stake the minted 83,440.57 WBNB+BOG LP tokens into the BOG token contract for profit sharing.

> Step 3: Perform 434 self-transfers in the total transfer amount of 18.74M BOG, resulting in an increased balance of 151K BOG.

> Step 4: Sell the extra BOG to WBNB, and then to anyETH.

> Step 5: Remove the added liquidity in Step 1 and complete the flash-swaps.

### [peckshield medium](https://peckshield.medium.com/bogged-finance-incident-root-cause-analysis-718d53faad5c)

## Cream (again) - August 2021 - losses `$25M`

AMP is a ERC77-based ERC1820 token that, upon it's introduction, had a _reentrancy_ bug. 

> “The hack is made possible due to a reentrancy bug introduced by \$AMP, which is an ERC777-like token and exploited to re-borrow assets during its transfer before updating the first borrow.”

> This was flashloan exploit where hacker took a flashloan in ETH and used that loan to borrow AMP tokens. PeckShield explained the attack as:

> “Specifically, in the example tx, the hacker makes a flashloan of 500 ETH and deposit the funds as collateral. Then the hacker borrows 19M \$AMP and makes use of the reentrancy bug to re-borrow 355 ETHs inside \$AMP token transfer (). Then the hacker self-liquidates the borrow.”

### [news](https://crypto-economy.com/defi-lender-cream-finance-suffers-a-25m-flash-loan-exploit/)

# Mitigation

## bZx-like

### Human error 

> It should be noted that this [margin pump] step should be thwarted by the built-in sanity check, which verifies the position will not go default after the swap. However, this check did not kick in when the attack occurs... _(- [Peckshield](https://peckshield.medium.com/bzx-hack-full-disclosure-with-detailed-profit-analysis-e6b1fa9b18fc))_

One might conclude that this attack is blameable on a programming paradigm that bets it all on the programmer writing assert logic correctly. But let us not be lured into a false sense of security just because we have Plutus! 

### Oracular assumptions

There are two basic ideas here. There's the integrity of the DeX and the protection of the broader ecosystem. I think the likelier threat is that Danaswap could be lured into false beliefs the way UniSwap was lured into false beliefs, even if the Dana price does not get gamed.

It appears to me that bZx's mistake was using DeX price data as a source of truth (in the margin trading function). The questions for us are: 
- how could someone else's margin trading-like function, if they make the same mistake bZx made, pump Danaswap beliefs/prices? 
- Is there anything uniquely risky about Dana on this vector?
- Does the gears of pool picking make this threatmodel better, worse, or just the same?

Isaac suggested we could **block price manipulation by disallowing mid-transaction information from updating prices**. Let's talk about this on call, keen to hear if anyone thinks this won't work. 

## Harvest-like

Isaac suggested we could **block price manipulation by disallowing mid-transaction information from updating prices**. Let's talk about this on call, keen to hear if anyone thinks this won't work. 

## Homora-Cream-like

## Pancake Bunny-like

### Human error

This just looks to me like the software was incredibly bad. There doesn't seem to be a mechanism design lesson here. 

## Bogged-like

## Cream-like

# Summary

I think the following types of risks are distinct

1. Risks to Dana holders and the Ardana core stakeholders
2. Risks to our neighbors in the ecosystem that we want to protect them from
3. Risks that everyone should be empowered to take, different use of the word "risk" to mean financial/gambling risk. 

At the mechanism design level, it's possible that Isaac's idea will be sufficient. However, implementation mistakes could still be very costly. 
