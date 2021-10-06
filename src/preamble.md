\chapter{Preamble}

The audit is a preliminary effort to compensate for the fact that proper formal verification before launch is infeasible. 

An audit means many things. Let's be precise about what we mean by audit in this document.

\begin{definition}
An $\textbf{audit}$ is a document provided to the community to guide them in taking informed risk.
\end{definition}
\begin{definition}
A $\textbf{community}$ consists of liquidity providers, investors, swappers, arbitrageurs, governance token holders, and neighboring members/projects of the ecosystem.
\end{definition}

## Desiderata
* **The community is the audience. The community is the customer.** 

* I think we want to make an explicit demarcation of risks for whom. Some risks only effect Ardana internally, other risks effect the collective of Dana holders, other risks effect our neighbors in the ecosystem. I think there's a difference between risks we want to eliminate and risks we want to empower the community to take. I'm sort of imagining profiling these as separate _axes_ of risk. The idea here is that I'm frustrated with the literature because it almost feels like it uses the word "attack" anytime someone loses money. This is not adequate- sometimes you just gambled and lost, sometimes the "attacker" followed the rules of the mechanism as designed. There's a morality/values question to each attack, and **the audit needs to provide disambiguation and clarity without taking sides on each values/morality question**. 

* The audit is **as much as was possible to do before launch time, not exhaustive**.

# Considerations

In this chapter we look at broad concepts and decisions and provide context into the way the team is thinking about them. This section should add indirect value to the process of taking informed risks.

# Attacks

In this chapter we profile threat models, attack vectors, vulnerabilities; mostly on the economic and mechanism design levels, but occasionally on the software implementation level. 

This audit will take on a bit of a code-is-law opinion; many things which are called "attacks" are in fact people using mechanisms as designed. However, it is still the responsibilty of a platform (such as a DeX) to help the community make informed decisions about risk, even when the risk concerns unforeseen behaviors of a protocol or implementation. 

Philosophically, be wary of morally charged language in the overall literature. It often implies that an attack is carried out by a summary enemy of the entire ecosystem, that the ecosystem is victimized, when clearer thinking shows that a small team or platform was the sole victim. 
