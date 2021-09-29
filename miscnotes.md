# Miscellaneous notepad

- "arbitrage opportunities tend to decrease as liquidity increases" - finematics, how not to get rekt, 8:00


## concurrency solution
- **a nice property:** if two people perform the same action at the same time, that action should be performed at the same price.
- **weaker form**: _chance_ oughtn't make one a winner and another a loser.
- **this guy's concurrency solution**: two utxos: a transaction plan that calculates what the actual amounts will be, second one that actually executes. 
- "would rather try to prevent scenarios where everyone's pulling out liquidity at the same time, because that would mean we failed, than prove properties about that scenario"
