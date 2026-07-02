# TLA+ Proof / Symbolic Tools (W0.2)

Environment: macOS (Darwin 25.3.0), arm64 (Apple Silicon), Java = Temurin OpenJDK 25
(`/Library/Java/JavaVirtualMachines/temurin-25.jdk/Contents/Home`).

Neither tool has a Homebrew formula (`brew install apalache` / `tlaps` both fail:
"No available formula"). Both were installed from GitHub release binaries into this
directory. Binaries/dists are gitignored; only this file, `.gitignore`, and `smoke/`
sources are tracked. Re-provision with the download commands below.

---

## 1. Apalache (symbolic model checker)

- **Version:** 0.58.2 (build 850292f)
- **Binary:** `/Users/eric/GitHub/prove-TLA/tools/apalache-0.58.2/bin/apalache-mc`
- **Install:**
  ```sh
  cd /Users/eric/GitHub/prove-TLA/tools
  curl -sL -o apalache.tgz \
    https://github.com/apalache-mc/apalache/releases/download/v0.58.2/apalache-0.58.2.tgz
  tar xzf apalache.tgz   # -> apalache-0.58.2/
  ```

### Smoke test

```sh
cd /Users/eric/GitHub/prove-TLA/tools/smoke
/Users/eric/GitHub/prove-TLA/tools/apalache-0.58.2/bin/apalache-mc \
  check --length=5 --inv=Inv Counter.tla
```

Output (tail):

```
State 5: state invariant 0 holds.
The outcome is: NoError
Checker reports no error up to computation length 5
Total time: 1.335 sec
EXITCODE: OK
```

### Caveats

- **Java 25 works.** No compatible-JDK install was needed; no `JAVA_HOME` override
  required. The JVM prints deprecation warnings
  (`sun.misc.Unsafe::objectFieldOffset has been called by
  com.google.common.util.concurrent.AbstractFuture...` — from Guava inside
  `apalache.jar`). Harmless today, but `sun.misc.Unsafe` "will be removed in a
  future release", so a future JDK may break this jar; fallback is
  `brew install --cask temurin@17` and `JAVA_HOME=$(/usr/libexec/java_home -v 17)`.
- **Type annotations are mandatory.** Apalache's Snowcat type checker rejects
  untyped variables (`type input error: Expected a type annotation for VARIABLE x`).
  Every `VARIABLE`/`CONSTANT` needs a `\* @type: ...;` annotation
  (see `smoke/Counter.tla`).
- Run artifacts go to `_apalache-out/` next to the spec (gitignored).

---

## 2. TLAPS / tlapm (proof manager)

- **Version:** 1.6.0-pre (arm64-darwin release asset published 2026-06-18;
  `tlapm --version` prints the git hash `80172c6`)
- **Binary:** `/Users/eric/GitHub/prove-TLA/tools/tlapm/bin/tlapm`
  (also `tlapm_lsp`, `translate` in the same dir)
- **Bundled prover backends** (`tools/tlapm/lib/tlapm/backends/`): zenon, z3, ls4,
  and a full Isabelle distribution — no separate installs needed.
- **Install:**
  ```sh
  cd /Users/eric/GitHub/prove-TLA/tools
  curl -sL -o tlapm-1.6.0-pre-arm64-darwin.tar.gz \
    https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-arm64-darwin.tar.gz
  tar xzf tlapm-1.6.0-pre-arm64-darwin.tar.gz   # -> tlapm/
  ```

### Smoke test

```sh
cd /Users/eric/GitHub/prove-TLA/tools/smoke
/Users/eric/GitHub/prove-TLA/tools/tlapm/bin/tlapm ProofSmoke.tla
```

Output (tail):

```
[INFO]: All 2 obligations proved.
```

(The spec proves `1 + 1 = 2` and `\A p \in BOOLEAN : p \/ ~p`, both via `OBVIOUS`.
With `--toolbox 0 0` you can watch per-obligation status; obligation 1 fell through
to the Isabelle backend and was still proved — first Isabelle run is slow, ~6 s,
while later runs hit the fingerprint cache.)

### Caveats

- **1.6.0-pre is a prerelease.** It is the only arm64-macOS build available — the
  last stable release (1.5.0, 2022) ships only a 32-bit `i386-darwin` installer,
  which cannot run on modern macOS at all. No opam/source build was needed.
- The classic 1.5.0 route and `brew install tlaps` are both dead ends on this
  machine; treat the GitHub `1.6.0-pre` tag as the canonical source.
- Proof caches go to `.tlacache/` next to the spec (gitignored).
- Trivial arithmetic sometimes needs Isabelle rather than zenon/z3; expect the
  first cold run of a proof to take seconds, not milliseconds.

---

## Convenience

Add to a shell session (or a project script) when working here:

```sh
export PATH="/Users/eric/GitHub/prove-TLA/tools/apalache-0.58.2/bin:/Users/eric/GitHub/prove-TLA/tools/tlapm/bin:$PATH"
```

## 3. tla2tools.jar (SANY+TLC)
- Pinned at tools/tla2tools.jar (latest GitHub release, fetched 2026-07-02). The jar in tla_benchmark/ is SANY 2.2 (2020) and mis-parses TLAPS proof syntax - do not use.
- CommunityModules-deps.jar + tlapm stdlib + tools/extra-modules/Apalache.tla are on the module path (see harness/runner.py).
