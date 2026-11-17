# github-core-clone

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/phoenixseiya17/github-core-clone/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/phoenixseiya17/github-core-clone/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A GitHub-compatible git forge in a single Python 3 stdlib file (`main.py`).

One process serves, from an in-memory store:

- **Git smart HTTP** — upload-pack v2 (`ls-refs`, `fetch`, shallow/deepen,
  `unshallow`, sideband) and v0 advertisement, receive-pack v0 with
  `report-status`, pack read/write with OFS/REF delta resolution.
- **REST v3** — repos, refs, branches, commits, contents, labels, issues,
  comments, pull requests (incl. squash merge + conflict detection),
  pagination via `Link` headers.
- **GraphQL** — hand-rolled parser + executor: repositories, issues,
  pull requests, mutations, cursor pagination, introspection (`__type`).
- **MCP** — JSON-RPC 2.0 Streamable HTTP, modern era `2026-07-28`
  (`server/discover`) plus legacy `initialize`; repo/issue/PR tools.

State is fully deterministic: no wall-clock timestamps or random values in
any observable state (fixed epoch for REST-created commits, fixed
`merged_at`, deterministic counters).

Boot contract: binds an ephemeral port, `POST`s `{"port": N}` to
`$MAKEFUN_ENV_URL/register`, then long-polls `GET .../done` until the
environment is done, then exits 0. Without `MAKEFUN_ENV_URL` it serves
forever on the given port (local dev).

## Run it

```sh
python3 main.py [--port PORT] [--host HOST]
# env: MAKEFUN_ENV_URL, MAKEFUN_SHOP_TOKEN
```

## Files

- `main.py` — the whole forge (stdlib only, no git binary, no network beyond the suite)
- `LICENSE` — MIT

---

<sub>Entered on [make.fun](https://make.fun/?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
