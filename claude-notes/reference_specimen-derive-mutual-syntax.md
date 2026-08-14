---
name: specimen-derive-mutual-syntax
description: Specimen derive_mutual syntax reference — sorts, input/output conventions, options, and usage patterns
metadata:
  type: reference
---

## derive_mutual syntax

```lean
syntax mutualEntry := ("generator" <|> "enumerator" <|> "checker")? term
syntax "derive_mutual" mutualEntry,+ : command
```

### Conventions:
- **Inputs**: lambda-bound parameters (`fun x y => ...`)
- **Outputs**: existentially quantified (`∃ (z : T), ...`)
- Default sort is `generator` if no keyword prefix
- Multiple entries are comma-separated

### Key options (set before the command):
- `set_option specimen.autoDeriveDeps true` — auto-discover and derive transitive deps
- `set_option specimen.multiOutput true` — allow multi-output hypothesis steps

### Examples:
```lean
-- Generator with inputs G, t and output e
derive_mutual (fun G t => ∃ (e : term), typing G e t)

-- Checker with all inputs
derive_mutual checker (fun Γ e τ => typing Γ e τ)

-- All outputs (no inputs)
derive_mutual (∃ (Γ : List type) (e : term) (τ : type), typing Γ e τ)

-- Multiple entries with mixed sorts
derive_mutual
  generator (fun τ => ∃ (Γ) (e : term), typing Γ e τ),
  checker (fun Γ e τ => typing Γ e τ)
```

### Testing derived instances:
```lean
#eval Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun e => typing [] e (.Fun .Nat .Nat)) 3) 3
```

### Source: `/local/home/segevem/specimen/Specimen/DeriveConstrainedProducer.lean`
