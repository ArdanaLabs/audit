# Wallet integration

Ardana is partnering with [Emurgo](https://emurgo.io/), such that the [Yoroi](https://yoroi-wallet.com/#/) wallet is the means by which users interact with `Danaswap`. A user's balance of Ardana stablecoins can be found in their Yoroi wallet. 

According to [a video published November 14, 2021](https://youtu.be/j9wvmi0HGu0), Project Ardana recommends using Yoroi as a browser extension in Brave (a browser derived from Chromium). As of this writing, Yoroi offers browser extensions in Chrome, Edge and Firefox, as well as smartphone apps for Android and iPhone. 

Yoroi's [security assurances](https://yoroi-wallet.com/#/faq/4) imply that they take security seriously. Of note is their private key storage: encrypted on users' machines, never on third-party servers, nor even shared with Yoroi. 

## Yoroi audit

Yoroi claims to have been rigorously audited. 

> Yoroi is a light wallet for Cardano. It’s simple, fast and secure. Yoroi is an Emurgo product, engineered by IOHK. It follows best practices for software in the industry, including a comprehensive security audit. 

However, it seems artifacts (such as reports) from this audit are private, as of this writing. 

## General security in working with browser extensions 

The advanced and wary reader may see [@BrowserExtensions] to further scrutinize Yoroi. Additionally, assurances in \ref{section:frontend} should also contribute to anyone's assessment that the end-to-end user experience is secure, because the interface between Ardana's website and Yoroi will be continuously monitored via the `npm audit` database. Additionally, we recommend the reader see [@PersonalSecurity] and implement at least some of its advice before working with wallets. 
