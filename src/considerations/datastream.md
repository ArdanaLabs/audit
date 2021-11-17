# Datastream integrity

Ardana stablecoins need to monitor the price of the asset they're pegged to in order to self-regulate their price and stay current. This introduces dependence on a datastream, which the team calls an **oracle**. As such, some third party service needs to be interfaced with, such as Coinbase's or Binance's APIs. 

The team assures the authorship of the current document that the following measures are taken. 

1. Not relying on DNS lookup to connect to the thirdparty datastream. 

2. API requests are signed, so an attacker can't spoof the IP of the data source. 

3. Frequent use of a key rotation mechanism. 

4. Moving to decentralized oracle as quickly as possible after launch (which is already designed for). 

I am making the following further recommendations

1. We want a plan in place to detect upstream attacks (i.e. listen for the data source's announcements when they've been attack), propagate freezes of some kind through our system in that event. 

2. Correlating multiple data sources and pegging downstream behavior to agreement of multiple sources.

#### Chaos theory

There's a sense in which if Ardana is successful, then the price of `DANA` and, say, `dUSD` will be an input to the international multivariate "function" that is the price of `USD`. If that "function" were to be an input to the price of `dUSD`, this would technically lead to a positive feedback loop. However, we don't think much can be said about it. Intuitively, prices of just about anything are subject to the same positive feedback loop, and nothing too "weird" seems to happen unless you consider the entire economy to be in a "weird" state. At that point, one would have troubles far exceeding the note about datastreams. 
