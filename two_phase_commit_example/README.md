# Two Phase Commit Protocol Example

Here's a more realistic and complete example, with the generated code for the `TwoPhaseCommit.tla` specification. It includes an special oracle that works as a transaction manager, and a code for simulating some resource managers.

The intention here is to run each manager on a separate terminal emulator (or even machine!). First run the model with the oracle as a transaction manager:
```sh
iex --sname "oracle@localhost" --cookie auth -S mix
```

Then start some managers, each on its own window:
```sh
iex --sname "manager1@localhost" --cookie auth resource_manager.ex "r1"
iex --sname "manager2@localhost" --cookie auth resource_manager.ex "r2"
```

When everything is up and running, hit `Enter` on the first terminal prompt and start playing around choosing actions on any prompt, the order doesn't matter - that's the whole point of TLA+ :D
