# Elixir Environment

This is a bootstrap mix project where the generated code can be ran, with some oracle examples to help simulate interaction with multiple processes.

The default oracle will read input each time it needs help choosing the next action. If you change the Oracle spawned by the generated code to the `RandomOracle`, the choices will be done randomly with a 1 second interval so the output is human readable.

Run with `mix`
