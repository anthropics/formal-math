# Improved certificate import-closure acceptance criteria v2

This is a conditional alternative to v1 (`ARCHITECTURE-ACCEPTANCE.md`, SHA256 `18e023b1ceafd677cfa2e9dc849f68181572bf24eb947b17c5ae8cc14a3d858f`). It does not edit or silently weaken v1. V2 permits reuse of `Zeta23.ThmD.Sextuple.Macro.Layout` only after the shared format refactor below passes every exact-delta and closure check.

## Accepted architecture

1. New lightweight `Zeta23.ThmD.Sextuple.Macro.TreeFormat` imports `Zeta23.ThmD.Sextuple.AffineTree` and owns exactly:
   - `leafWordBits : ℕ := 321`
   - `leafBlockSize : ℕ := 256`
2. Baseline `Macro.TreeReader` replaces its direct `AffineTree`/format ownership as needed with an import of `Macro.TreeFormat` and removes only the two now-shared local definitions. Their fully qualified names, types, bodies, reducibility, and namespace remain unchanged.
3. `Macro.Layout` changes only its import from data-bearing `Macro.TreeWords` to lightweight `Macro.TreeFormat`; its declarations and proofs remain otherwise source-identical.
4. Qualified `ImprovedTreeWords` imports `Zeta23.ThmD.Sextuple.AffineTree` directly and never imports baseline `Macro.TreeReader` or `Macro.TreeWords`.
5. Qualified `ImprovedLayout` may import the refactored `Macro.Layout`.

## Exact source/API delta gate

Freeze before/after sources and hashes. An independent normalized diff must establish:

- `TreeFormat` contains no data, catalog, scalar, reader, layout, or certificate imports and no declarations beyond the two exact format constants (apart from comments/namespace scaffolding).
- The moved constant declarations are byte-equivalent after normalization to the prior frozen `Macro.TreeReader` declarations.
- `Macro.TreeReader` changes only its import set and deletion of those two declarations. Decoder, stream, checker, path, soundness theorem, namespaces, and options are unchanged.
- `Macro.Layout` changes only the single direct import `Macro.TreeWords` → `Macro.TreeFormat`. All definitions/theorems and their text are unchanged.
- No duplicate declaration of `leafWordBits` or `leafBlockSize` exists in the resolved environment.
- `#check`/`#reduce` probes confirm the same fully qualified APIs and exact values 321/256. Baseline TreeReader and Layout rebuild successfully.

Any extra semantic delta rejects v2 and returns the gate to v1.

## Direct-import requirements

- Qualified `ImprovedCatalog` imports lightweight `Macro.StableCatalog`, not baseline `Macro.ScalarData`.
- Qualified `ImprovedTreeWords` imports `AffineTree` directly, not `Macro.TreeReader` or `Macro.TreeWords`.
- Qualified `ImprovedLayout` imports the refactored `Macro.Layout`; it must not import `Macro.TreeWords`, `Macro.TreeReader`, or `Macro.ScalarData` directly.

## Resolved whole-certificate closure

Compute both a recursive source-import closure and Lean-resolved `--deps`/`--src-deps` closure for:

- qualified ImprovedCatalog/TreeReader/TreeWords/Layout,
- every final chunk and assembly module,
- final Certificate/root theorem.

The resolved closure must exclude, both directly and transitively:

- `Zeta23.ThmD.Sextuple.Macro.ScalarData`
- `Zeta23.ThmD.Sextuple.Macro.TreeWords`
- `Zeta23.ThmD.Sextuple.Macro.TreeReader`

`Zeta23.ThmD.Sextuple.Macro.Layout` is allowed only at its frozen refactored hash and only if its own resolved closure is exactly data-independent through `Macro.TreeFormat`/`AffineTree` (plus standard proof-library dependencies). A stale pre-refactor `Macro.Layout.olean` is forbidden. Hash the resolved Layout source and `.olean` used by every build.

Other analytic/schema/envelope modules are allowed only when deliberate and listed. No banned module may enter through them.

## Rebuild and hostile regression

With repo-shadow qualified modules first in `LEAN_PATH` and stale relevant `.olean` files excluded:

- build TreeFormat, refactored baseline TreeReader, refactored Layout, StableCatalog, ImprovedCatalog, ImprovedTreeReader, ImprovedTreeWords, and ImprovedLayout;
- rerun the pinned 99-token/50-payload calibration;
- rerun representative chunks covering sizes 1/37/99, depths 2/12/16/34/74, tail-only/quadratic-only/mixed, and first/final cursors;
- rerun hostile term/anchor/cursor, topology/leaf-layout, and out-of-range `Fin 5` probes;
- require only `propext`, `Classical.choice`, and `Quot.sound` for successful certificate theorems; the one-past `Fin 5` probe must fail without `.olean`.

## Byte and theorem invariance

Raw streams, packed payload, plan, numeric arrays, 31 data modules, path/cursor statements, calibration statement, and root DAG remain unchanged except qualified import/module names. The refactored generic layout predicates and proofs must elaborate to the same statements. Any certificate-data or theorem-statement delta reopens the full audit.

Passing v2 authorizes the owner full build. It does not replace inspection of every final chunk/assembly/root source, log, `.olean`, closure record, or axiom printout.
