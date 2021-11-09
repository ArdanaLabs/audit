# Price manipulation \label{section:pump}

\begin{definition}[Truthfulness of a protocol's beliefs]\label{dfn:truebeliefs}
A protocol $\Pi$ beliefs are \textbf{true} when it's prices are accurate.
\end{definition}

\begin{definition}[Price manipulation]\label{dfn:pump}
Given an exchange protocol $\Pi$, an attacker \textbf{manipulates prices} when they 
\end{definition}

## Price manipulation on `Danaswap` costs more than it's worth

DRAFT: 
you want to extract value from the system by making trades
1. trade in one direction to drive the exchange rate low in one direction, then buy back in the other direction. 
2. **assuming** a sufficient community (wait this isn't going anywhere)
3. the only way to extract money from a system is to bring the system closer to equilibrium, where eqilibrium is the V(a) = V(b). 

The only way you could "extract value" is if you had a state (x:A,y:B) and transitioned to a state of (x - delta:A, y:B) rather than (x - delta:A, B + delta: B). Which is invalid by the invariant.


a huge trade will skew the exchange rates

anything that someone does will be evened out by the community of arbitrageurs, who will profit from fixing the situation.



\begin{belief}[Infinite money attack is the only "pump" scheme]\label{blf:infiniteattackonly}
The infinite money attack is the only way to make \texttt{Danaswap}'s beliefs less true.
\end{belief}
While the limit case is extreme, it illustrates the resilience of `Danaswap` to margin pump -like exploits.

