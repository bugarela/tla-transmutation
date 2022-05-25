# TLA+ Transmutation
Elixir code generation from TLA+ specifications

I've started to work on this for my bachelor thesis, which can be found [here](https://github.com/bugarela/bachelor-thesis) (Portuguese only).

The formalization of the translation rules are available at [rules.pdf](rules.pdf)

Notice that this covers only a small portion of TLA+ definitions and it is yet to be incremented with more translations. The Parser itself isn't able to recognize much. Contributions are welcome :D.

## Dependencies

> For nix users, there are nix files for both a Haskell and an Elixir environment.

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

This currently supports partially 2 forms of parsing:
1. From `.tla` files: this is deprecated and supports a minimal fragment of the language
2. From `.json` files produced by [Apalache](https://github.com/informalsystems/apalache)'s parsing: Work in progress.

To generate code, specify the args:
1. Mode (`tla` or `json`)
2. Filepath (for the `.tla` or `.json` file)
3. Init definition name (i.e. `MyInit`)
4. Next definition name (i.e. `MyNext`)

Some examples:
```sh
./Main json tla_specifications/token-transfer/TokenTransfer1.json Init Next
```

``` sh
./Main tla tla_specifications/EfetivacaoEmDuasFases.tla DFInit DFNext
```
