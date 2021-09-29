# Preamble

## On the approach
There are a number of ways to go about this. 

The first way we talked about was to provide a list of desirable properties and find ways to verify or validate them. This is a sort of _positive approach_, it talks about things we want. 

Another angle is for me to write up my understanding of all the ecosystem functionalities one at a time and point out some threatmodels along the way. This is a sort of _negative approach_, it talks about things we don't want.

The problem with both approaches is the distance between _pointing out_ properties and _implementing/defending against them_ depending on if it's the positive or negative case. Also keep in mind that in some sense the audit is a "warmup" for a post-launch formal verification. 

## Desiderata
* **The community is the audience. The community is the customer.** 

* I think we want to make an explicit demarcation of risks for whom. Some risks only effect Ardana internally, other risks effect the collective of Dana holders, other risks effect our neighbors in the ecosystem. I think there's a difference between risks we want to eliminate and risks we want to empower the community to take. I'm sort of imagining profiling these as separate _axes_ of risk. The idea here is that I'm frustrated with the literature because it almost feels like it uses the word "attack" anytime someone loses money. This is not adequate- sometimes you just gambled and lost, sometimes the "attacker" followed the rules of the mechanism as designed. There's a morality/values question to each attack, and **the audit needs to provide disambiguation and clarity without taking sides on each values/morality question**. 

* The audit is **as much as was possible to do before launch time, not exhaustive**.

We should also clearly define what we think a secure DeX even is.
