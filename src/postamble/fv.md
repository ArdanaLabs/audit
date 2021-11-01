# Toward formal verification

I was hired as a logician on the merit of my coq skills, but formal verification was considered to time-intensive to do before launch. Producing this document was seen as a sort of warmup for FV. Now that we're launched, we will begin a formal verification stage of the project. 

Properties we'd like to prove

1. Every transaction **worth `>=0$` to liquidity provider**, for some asset `$`. 
2. **Non-indebted pools are never liquidated**.
3. **"No money for nothing"**: no one can arbitrarily withdraw assets from the protocol without depositing something else or paying some fee. 
4. **Modular resilience**. In the language of [@CompositionalityModularity], **modular risk** of a composite contract is risk that is greater than the sum of the risks of the individual lego blocks. We would like not just for the Ardana project to be **compositional** (i.e. the sum risk is _no more_ than the sum of the risks of the individual lego blocks), but for it to be compositional with respect to actors that may interact with it, arbitrarily.
5. It costs nearly infinite money for an attacker to make `Danaswap`'s beliefs untrue. 
