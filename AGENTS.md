Lean-Inf Agents and MCP Setup

- Purpose: use MCP to drive Lean LSP for quick symbol search, go-to-def, and spammy elaboration pings while iterating. We intentionally surface elaboration errors early, then refine data structures.

- MCP server: `uvx lean-lsp-mcp` (configured in `.mcp/config.json`). Any MCP-capable client can spawn it from the repo root.

- Typical workflow:
  - Run `lake build` to get rich feedback and elaboration errors.
  - In parallel, spam the MCP LSP tool (`lean-lsp-mcp`) to query types, holes, and goals while editing. Expect lots of transient errors — that’s intended signal.
  - Iterate on definitions after we’ve captured the current error surface.

- Notes:
  - Toolchain is set to latest Lean nightly via `lean-toolchain`.
  - If `uvx` is not installed, install `uv` first (https://docs.astral.sh/uv/), then run `uvx lean-lsp-mcp`.
  - MCP JSON is project-local so different clients can pick it up without per-user config.
  - The `grind` tactic (see Lean reference) is a good fit for small algebraic/data-structure goals. We’ll adapt the index map example to show that inserting into the infinitesimal/infinite maps preserves the sign in our `signum` definition, once the structures are stabilized.

Next Run Plan (Code > Proof)

- Generalize LC incrementally over generic coefficients while keeping Rat as default.
- Replace `Term`/`CoeffMap` with `TermG`/`CoeffMapG` (Rat aliases) in `LeviCivitaNum.lean`.
- Route LC arithmetic via `Polynomial` (alias of `PolynomialG Std.Internal.Rat`).
- Add zero-term pruning to `PolynomialG` and use it in formatting/equality.
- Re-enable selected `#eval` (non-bang) to show progress; keep `#eval!` off sorry paths.
- Defer proofs; do not import `LeanInf/SignLemmas.lean` yet.

Proofs (grind/mvcgen) game plan

- Prefer keys-based invariants (Prop over `HashMap.contains`) so Std lemmas (`contains_insert`, `contains_map`, `mem_toList` bridges) compose with `grind`.
- Verify functions Hoare-style with `grind` by case-splitting on branch lemmas. If one branch doesn’t close, rename it to `_` and extract a tiny helper (per the hackmd notes) to finish that case.
- New scratchpad: `LeanInf/GrindHoare.lean` (NOT imported). Minimal `KeysNeg` + insert/map proofs using `grind` and Std HashMap lemmas. Use this file to iterate `mvcgen`/`grind` ideas without touching the build.
- Merges: implement fold-based `mergeAdd` over `toList`; prove invariants by list induction using `contains_insert`; `grind` should close the subcases.
- toLC plan: build `collectNeg/collectPos` via guarded folds and prove `KeysNeg/KeysPos` with `grind`, then construct LC from those; or iterate insert-preservation over the partitioning loop.

Validation discipline

- Run `lake build` after each meaningful patch to catch import cycles or regressions early. Keep experimental grind/mvcgen code in non-imported files until stabilized.

Key Files

- `LeanInf/CoeffLike.lean`: minimal class for coefficient-like types (`isPos/isNeg`), instances for core Rat and Float.
- `LeanInf/PolyGeneric.lean`: generic polynomial `PolynomialG α` + ops (`Add/Neg/Sub/Mul/OfNat/OfScientific/ToString`).
- `LeanInf/LeviCivitaNum.lean`: current Rat-based LC; includes `toPolyG` bridge to `PolynomialG` for migration.
- `LeanInf/LCGeneric.lean`: WIP generic LC — intentionally not imported to keep builds green.
- `LeanInf/SignLemmas.lean`: proof stubs (grind-based) — not imported yet.

Useful Commands

- Full build with rich logs: `lake build` or `lake build --fail-level=info`.
- Fast module check: `lake lean LeanInf/LeviCivitaNum.lean` (or any path).
- LSP via MCP: run your MCP client; it will spawn `uvx lean-lsp-mcp` from `.mcp/config.json`.

Numerics / Literals

- `OfScientific` is wired for core Rat, generic `PolynomialG`, and `LeviCivitaNum`.
- Decimal/scientific literals (e.g., `1.23`, `1.2e3`) work in coefficients; use `Std.Internal.Rat` in generic contexts.

Caveats

- Some `#eval` were commented to keep builds green; re-enable selectively when code paths are stable.
- Expect warnings from `sorry` placeholders in LC; they’re queued for a later proof pass.
- Prefer `emptyWithCapacity` for new `Std.HashMap` constructions (we’ve updated most call sites).
