# Toward formal verification

Formal verification (FV) was considered too time-intensive to do before launch. The authorship of the current document was seen as a sort of warmup for FV. Now that we're launched, we will begin a formal verification stage of the project. 

`Danaswap` validators are the first priority for formal verification. 

Other properties we'd like to prove

1. **Non-indebted pools are never liquidated**.
2. **"No money for nothing"**: no one can arbitrarily withdraw assets from the protocol without depositing something else or paying some fee. 
3. **Modular resilience**. In the language of [@CompositionalityModularity], **modular risk** of a composite contract is risk that is greater than the sum of the risks of the individual lego blocks. We would like not just for the Ardana project to be **compositional** (i.e. the sum risk is _no more_ than the sum of the risks of the individual lego blocks), but for it to be compositional with respect to actors that may interact with it, arbitrarily.
4. Proofs of results from \nameref{section:infinite}. 
