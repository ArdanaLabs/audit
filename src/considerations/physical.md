# Physical and operational security 

A dapp consists of on-chain and off-chain components. An ecosystem like Cardano's confidence in the security properties, by construction or otherwise, of its underlying decentralized technology (sometimes called "layer one") is fundamental, so we do not discuss it here. On that, we can point to [entrypoint literature for the unfamiliar](https://why.cardano.org/en/introduction/) and for the advanced reader [@Ouroboros].

Dapp developers are responsible for securing off-chain dapp components. Ardana's CTO composed a treatment of the team's security considerations in [@SecuringArdanaSwap]. In what follows, we assume the reader has a minimal understanding of the [Plutus Application Backend (PAB)](https://github.com/input-output-hk/Alonzo-testnet/blob/main/explainers/PAB-explainer.md).

The highlights are simple: 

1. No Virtual Machine (VM), no VM-to-VM attack. Ardana PABs run on bare metal.

2. Keys are both hosted and generated in the [Yubi Hardware Security Module 2](https://www.yubico.com/product/yubihsm-2/) (HSM). Keys on HSM cannot be read off the device. 

3. Developers who need to deploy are provisioned [Yubikey 5](https://www.yubico.com/products/yubikey-5-overview/), a physical authentication instrument, without which Ardana deployments are blocked. 

4. The bare metal is located in a Flexential data center, which is [thoroughly audited and certified for compliance according to numerous sets of industry standards](https://www.flexential.com/system/files/file/2021-03/centennial-flexential-data-center-data-sheet.pdf)[](https://www.flexential.com/compliance-certifications-and-attestations). 

5. [Cloudfare's DDOS protection](https://www.cloudflare.com/ddos/).

6. VPN: A [Tailscale](https://tailscale.com/) implementation of [Wireguard](https://www.wireguard.com/). 

7. Firewall

8. A port knock sequence provides an additional layer of access verification. 

## Personal protection 

Of course, it is up to individuals in the \nameref{dfn:community} to exercise strong digital security like password hygiene, etc. See [@PersonalSecurity] for a reasonably complete treatment. 
