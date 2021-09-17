# Audit Roadmap

**I have CC'd the list of desirable properties to "The Pile"](https://github.com/ArdanaLabs/audit/issues)**

_Notes about the approach moved to [README.md](https://github.com/ArdanaLabs/audit)_

## List of desirable properties (DEX)

### No Money For Nothing (NMFN)
NMFN is an intuitively desirable, if a little obvious, property. We do not want people to be able to arbitrarily withdraw assets.
#### Deliverable
There are a few ways to approach this
1. Enumerating people who think they're clever but ultimately get blocked
2. _Informally_ state and prove a NMFN theorem (perhaps a warmup for formally doing it later)
3. Assume NMFN property of stableswap and prove that the delta between DanaSwap and Stableswap preserves the property
   - Model dex as a game; correlate different sequences of play with eachother, see if that implies the payoffs correlate. See [bisimulation](https://en.wikipedia.org/wiki/Bisimulation)

#### Window
3. let's take 1 week pass and see where we're at

#### Notes
An approach to the predicate: show that any transaction does not decrease the liquidity token value of the dex. Finite enumeration of the ways the value of the dex could be decreased.  

### we want every transaction to be worth `>= $0` to the liquidity provider
**Rather redundant if NMFN goes well, omitting Deliverable/Window/Notes**

### Non-liquidation of non-indebted pools
**Cascading liquidations: how bad is it and what can we do to stop it?** Cascading liquidations is when liquidation of one asset causes other assets to liquidate, causing propagation of liquidation across the pools in the DEX. The following property is an attempt to articulate a solution: 

We would like for it to be not possible to liquidate a vault that is not in debt

#### Deliverable
Still can't think of a way to do this informally / at the spec level. It's probably possible to do formally with respect to implementation code. 

#### Window
I don't know how to do this pre-launch. If there are other DEXes that we think have this property we can take an assume-and-prove-the-delta-preserves approach like in NMFN approach 3, but I'm pretty sure other DEXes don't have this property. We can put a research task on my stack to find a DEX that has this property, or ask around the team. 

#### Notes
Youtube channel Finematics calls this a "Systemic risk"

### Modular resilience
Via the jargon of [Genovese 2018](https://blog.statebox.org/modularity-vs-compositionality-a-history-of-misunderstandings-be0150033568), _modular risk_ of a composite contract is risk that is _greater_ than the sum of the risks of the individual lego blocks. Morgan suggested
> I think the ideal way to handle these issues would be to use forms of reasoning which address how our system behaves for all possible systems of interacting actors of which it can be a part

We would like not just for the Ardana project to be compositional (i.e. the sum risk is _no more_ than the sum of the risks of the individual lego blocks), but for it to be compositional with respect to actors that may interact with it, arbitrarily.

#### Deliverable
A fully functional model of the DEX, a (informal) proposition quantified over it's input type. An approach is to implement a toy model and approximate the quantified proposition with property tests. There's a python flavor and a haskell flavor of this approach, perhaps each come with their strengths and weaknesses, but I know my audience ;). 

#### Window
let's take a 1 week pass and see where we're at. This is extremely ambitious as written down and might have to be iterated on or made more realistic.

#### Notes

