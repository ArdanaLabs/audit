# Stablecoin Specifications Distill

The following is a distillation of [utxo-design.md](https://github.com/ArdanaLabs/ardana-dollar/blob/main/utxo-design.md) and [endpoint-spec.md](https://github.com/ArdanaLabs/ardana-dollar/blob/main/endpoint-spec.md) provided by Quinn, original documents provided by Ben and others from mlabs. **Note**: occasionally distillation involves plagiarism.

As of 09-12

# endpoint-spec.md [original](https://github.com/ArdanaLabs/ardana-dollar/blob/main/utxo-design.md)

### Distinctions from MakerDAO
In general Ardana-Dollar is modelled on systems in MakerDAO (see [whitepaper](https://makerdao.com/whitepaper/White%20Paper%20-The%20Maker%20Protocol_%20MakerDAO%E2%80%99s%20Multi-Collateral%20Dai%20(MCD)%20System-FINAL-%20021720.pdf)), However, unlike MakerDAO:
- There will be a fixed number of DANA tokens (governance tokens) minted for all time
- Liquidation 'auctions' will run automatically in sync with Oracle updates with prices determined algorithmicly based on previous sales
- the role of keepers will be reduced in scope, instead these actions will be invoked by the oracle itself.
- the ardana-savings module will be launched seperately from the Ardana-dollar protocol, however the two protocols will integrate

### Architecture Summary

The ardana-dollar protocol will consist of 3 main smart contract components, each of which will have one or more schema subcomponents, and several individual scripts:
- Governance: this is intended to integrate with other Ardana services, or any other strategic partner that may need to provide rewards or know vote weight for DANA Token holders. This allows for extensible and upgradable Governance activities by isolating rewards and vote weight from proposal logic.
- The Central Treasury: This houses tokens that 'belong to the protocol', as well as the minting policy, and is crucial to allowing the Ardana-dollar protocol to have an upgrade path.  This portion of the project will integrate with future versions of the protocol without ever being upgraded.
 note: this serves as a treasury for the stablecoin protocol only, this will not integrate with the dex (though it MAY integrate with more than one stablecoin should they be launched.
- Stablecoin Protocol: This includes all scripts relating to a _particular version_ of the stablecoin protocol, the settings are managed by the Admin Validator, individual vaults manage collateral, the Buffer handles Seized collateral, liquidation, debt and surplus auctions, and the oracle brings off-chain pricing data onto the chain, triggering various asynchronous actions throughout the system
- Savings Module: This allows dUSD holders to reduce their risk by saving their dUSD tokens and collecting interest - it will integrate with the Buffer and Vault portions of the stablecoin protocol.

Additionally, there is one off-chain component needed:
- the Oracle Bot: listens via Websocket to one or more price feeds, and control a wallet, which will sign transactions to be verified on-chain.
- the Arbitrage Bot: Performs liquidations to the benefit of the user.

## Governance

### DanaStakePool Schema
This schema and the corresponding scripts are used to distribute rewards to users and, later, determine their voting power.

the democratic actions themselves can and will be delegated to other scripts and systems such that the Ardana Dex may integrate with this system.

- Deposit
- Withdraw
- QueryStakeBalance
- ProvideReward
- Query RewardBalance
- ClaimReward / DistributeRewards
- FinishRewardsForEpoch
- RegisterProposalFactory
- TriggerEpoch

## Ardana-Dollar Protocol

### Admin schema

The Admin Schema defines the types of actions that administrators might take to steer the stablecoin configuration

The Admin contract will need to keep track of a minCollateralRatio for each token type (this might just be a single value globally) - this may be something that DANA token holders will be able to update through a democratic process, which will need to adjust all vaults currently running as well as future vaults when changed

The Admin Contract will permit a single adminAddress to make adjustments to its config, this is one of the more centralized aspects of the system in v1 and will later be subsumed by democratic Proposal functions using vote weights from the Governance Contract in v2.

The Admin Contract is parameterized on a baseCurrency (this may be expanded to a record), such that the first and primary contract we will build uses "USD" to produce dUSD, but by deploying with a different parameter, we could easily use "JPY" to make dJPY etc. Each of these parameterized items would require a seperate Treasury, and by extension it's own DANA Float.

note: we may be able to extend the configuration of the treasury from a single contract address to a list, however this may require further examination and consideration.

all other structures in the ardana-Dollar protocol are parameterized on currency in this way, as is the oracle bot.

- Init-Vault
- UpdateAdminState
- InitiateUpgrade
- QueryAllVaults
- QueryBackedAmount

### Vault schema

The Vault schema represents a user's state on a single supported collateral type whose value can be obtained through a reliable oracle. Which collateral types are supported is decided by the AdminState.

Vault Config values: supportedToken :: AssetClass - tokens permitted for collateral use. minCollateralRatio :: Rational - default: (150%) - the minimum collateral/borrow value ratio permitted before liquidating an account's assets (ie the user can borrow 100 Ada worth of dUSD for every 120 Ada supplied as collateral) userAddress :: Address - the user address this vault is 'for' (other config values may be added for fee calculations, etc)

In practice, Collaterial Ratios are encouraged to be much higher than the minimum, more like 1:5 - 1:10. This insulates borrowers from price volatility and prevents liquidation events.

In order to compare collateral to the value of USD, we will require an Oracle. eventually this will require the use of an Oracle bot

Users can lock supported assets into their vault minting dUSD at a given collateral Ratio, users can return dUSD to the contract along with a collateral ratio to be maintained after the redemption (in the case of a partial redemption). This is also called a Collateralized debt position.

There will be many vault contract instances, each with a unique supportedToken - all of which mint dUSD.

the supportedToken for a vault may also be referred to as the underlying token of a vault.

Note: Although the Vault contract must be used to Mint new dUSD, the actual minting must also be approved by the Treasury, as the Treasury directly connects to the the MonetaryPolicy which will mint dUSD.

- AddCollateral
- RemoveCollateral
- AddBorrow
- RepayBorrow

### Oracle

- SetPrice

when a seizure occurs, the user's principle borrow is now equal to the nearestSafeLoanAmountInAda / DUSD:Ada Price the user's collateral is now newCollateralAmountInAda (converted back to the underlying currency) if this results in the user's collateral Ratio being less than minimumCollateralRatio we need to adjust this formula. the seized funds are sent to the liquidation module

this endpoint will rely on a bot which polls a centralized server, and controls a wallet to submit this information on-chain

calculating stability fees:

- each oracle call will calculate the POSIXTimeRange since the previous oracle call
- the stability fee Per vault will calculate the amount of interest against the principle to charge such that at the end of 1 year, the loan amount will be equal to the principal * (1 + stabilityForAssetClass) - this stabilityForAssetClass is the Ratio supplied along with VaultConfigs.
- this must always use the CURRENT stabilityFee, regardless of the one that was in place when the vault was created.

No Matter how many times SetPrice is called, this endpoint should only execute every 10 minutes

### BufferSchema

The Buffer algorithmicly runs 'auctions' to sell off collateral when a user falls below the minimumCollateralRatio

Additionally, it runs the Debt and Surplus auctions

- LiquidationPurchase
- DebtAuction
- SurplusAuction

## Treasury

### Treasury schema

The treasury holds all reserve funds, and other funds that belong 'to the protocol' and cannot be withdrawn directly by users, The treasury also manages the MonetaryPolicy used to mint dUSD such that upgrades to the ardana-dollar will not force a change in the monetaryPolicy used, as this would cause there to be 2 different 'dUSD' coins in circulation.

The treasury scripts will not receive upgrades, instead each version of the various Ardana-dollar scripts which integrate with it must receive a message from a centralized source (later, the ProposalFactories ), which will tell it to allow interaction with other scripts. Additionally, the treasury must control the MintingPolicy that mints dUSD and it also delgates this.

This module must function in such a way that the protocol can receive an upgrade without needing to trade in old DUSD from a previous protocol for new DUSD, or risking important funds being released

the treasury must track currentContract which is the contract that it delegates spending and DUSD minting operations to.

the treasury holds rewards and DANA tokens which are not yet issued to users, it also holds an amount of DUSD and DANA which are to be used exclusively for auctions.

Similar To the LiquidatonModule, the Treasury holds auctions where prices are determined algorithmicly

- DepositFundsWithCostCenter
- SpendFromCostCenter
- QueryCostCenters

## Oracle

this will be a small haskell program that integrates with an off-chain price feed from a centralized fiat currency exchange, ideally by websocket, alternatively by http polling.

upon price updates it will cryptographically verify the price feed signature, then sign a call to 'SetPrice', reformatting it to the plutus Data encoding

this bot will control a wallet, which will need to keep Ada on hand for transaction fees in order to guarantee regular oracle pricing updates.

# utxo-design.md [original](https://github.com/ArdanaLabs/ardana-dollar/blob/main/endpoint-spec.md)

Where the endpoint-spec describes the Schema design, this document will describe the Validators, and Monetary Policy scripts that those endpoints will call.

... 

Native tokens may be of several types
- Distributed tokens - tokens given to users may be fungible or non-fungible - these will always have a `$` prefix
- State tokens - used to manage and identify datum, either for a Validator script to use for scriptwide-state, or for a single user's state, in both cases, these are non-fungible
  State tokens 'for a user' generally indicates that the `address` or similar parameter must match that of the user.
- Permission Tokens - these tokens, by nature of being in a transaction, signify permission to perform a given type of action in some other component, this is used for extensible permission systems where validation of one action can be delegated to other scripts ad-hoc.
- Signed Tokens - These Tokens carry `SignedMessage tokenDatumType` rather than `tokenDatumType` and are signed by a designated wallet to signify off-chain authority on a particular topic. Typically used for data that would otherwise bottleneck the system.

Many State and Permission tokens function as witnesses to prove some prior event or state, or to show the provenance of other transaction data.

note: though `dUSD` is used below,  this is in fact a parameter-dependant token name based on `"d" <> Parameters.peggedCurrency`, by adjusting this and corresponding parameters throughout the protocol, we can easily create dGBP etc.
note: The different Address types each indicate how transactions should be authenticated
Address - This indicates a Script or a Wallet, we should verify that the transaction includes a utxo from this address OR is signed by the address
PubKeyHash - This indicates a wallet, we should verify that the transaction is signed by this PubKeyHash if necessary
ValidatorHash - This indicates a script, we should check for an included utxo from this address.

