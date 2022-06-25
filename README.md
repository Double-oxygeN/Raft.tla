# TLA+/Apalache Model Checking of Raft

**Raft** is a consensus algorithm designed for understandability.
Please see [the official Raft web page](https://raft.github.io/) for more information.

[**Apalache**](https://apalache.informal.systems/) is a tool for TLA+ model checking.

## Model Check

Before running the script, install Apalache according to [the instructions](https://apalache.informal.systems/docs/apalache/installation/index.html).

Run the script:

```sh
apalache check MC
```

### Invariants

Currently there is no invariants to be checked.

## License

The TLA+ document is [originally created by Diego Ongaro](https://github.com/ongardie/raft.tla),
under [Creative Commonse Attribution-4.0](https://creativecommons.org/licenses/by/4.0).

My revision is described on `Raft.tla` as comments.
