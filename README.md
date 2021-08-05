# TLA+ Transmutation
Elixir code generation from TLA+ specifications

I've started to work on this for my bachelor thesis, which can be found [here](https://github.com/GabrielaMafra/bachelor-thesis) (Portuguese only).

The formalization of the translation rules are available at [rules.pdf](rules.pdf)

Notice that this covers only a small portion of TLA+ definitions and it is yet to be incremented with more translations. The Parser itself isn't able to recognize much. Contributions are welcome :D.

## Dependencies
* GHC 8.0.2

#### For running the generated code
* Elixir
* Erlang

[Instructions for installation with asdf package manager](https://elixirgirls.com/install-guides/linux.html)

## Build
```sh
ghc Main.hs
```

## Run
```sh
./Main
```
Here is an successful execution example:
```sh
./Main
TLA spec path:
tla_specifications/Filename.tla
Initial state definition:
Init
Next state function definition:
Next
Elixir file written to elixir/lib/generated_code/filename.ex
```
