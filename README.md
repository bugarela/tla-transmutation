# TLA+ Transmutation
Elixir code and test generation from TLA+ specifications

## Dependencies

> For nix users, there are nix files for both a Haskell and an Elixir environment.

* GHC 8.0.2

#### For running the generated code
* Elixir
* Erlang

[Instructions for installation with asdf package manager](https://elixirgirls.com/install-guides/linux.html)

## Build

``` sh
make compile
```

## Run

The best parsing implementation takes JSON files previously parsed from TLA with [Apalache](https://github.com/informalsystems/apalache):

``` sh
apalache-mc parse --output=file.json file.tla
```

All compliled files (`CodeGenerator`, `WhiteboxTestGenerator` and `BlackboxTestGenerator`) take a single argument which is a JSON-formatted configuration file similar to [config-sample.json](./config-sample.json)

Folders inside [tla_specifications](./tla_specifications) are examples containing the required files for running the three executables. You can `cd` into any of them and run:

``` sh
../../CodeGenerator config.json && ../../BlackboxTestGenerator config.json && ../../WhiteboxTestGenerator config.json
```

