# Code quality

In internal documents, the Ardana team set engineering standards.

1. **Building with `nix`**. Properties of _immutable, reproducible_ builds are desirable and use of [`nix`](https://nixos.org/) for Cardano dapps is standardized across the ecosystem.

2. **Property tests**. These come in the categories domain-driven, tests of parser components, test of state machine components, integration property tests of database components, and also come alongside unit tests. Additionally, developers are made aware of coverage via continuous integration (CI). 

3. **Linting and code style**. Enforced via CI. 

4. GitHub practices of **code review and successful CI checks** for all merges into main, protected branches. 

5. No bottom type allowed. 

6. `newtype` constructor-destructor pairs rather than aliases and rather than passing around types like `String`, `Bool`, etc. 

## Frontend \label{section:frontend}

The frontend has a nice property that the javascript ecosystem has, unlike the haskell ecosystem, `npm audit` which queries a vulnerability database for everything in the build specification. This is a tool that the Ardana frontend team leverages in development, and that which will monitor and fix our build online through continuous delivery. The astute reader will see [@AdvisoryDatabase] for information about the vulnerability database `npm audit` relies on. 
