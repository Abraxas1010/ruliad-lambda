# Ruliad Lambda

**Machine-verified proofs for the foundations of λ-calculus ruliology.**

This repository contains Lean 4 formalizations supporting concepts from Stephen Wolfram's ["The Ruliology of Lambdas"](https://writings.stephenwolfram.com/2025/09/the-ruliology-of-lambdas/) (2025).

## Key Results

| Theorem | Description | Location |
|---------|-------------|----------|
| `Steps.churchRosser` | Church-Rosser (confluence) | `Lambda/Confluence.lean` |
| `Bridge.ofComb_simulates_step_joinable` | λ ↔ SK simulation | `Lambda/SKYBridge.lean` |
| `stepEdgesList` | Multiway enumeration | `Lambda/Beta.lean` |
| `enumTerms` | Term enumeration by size | `Lambda/Enumeration.lean` |

## Quick Start

```bash
# Clone
git clone https://github.com/Abraxas1010/ruliad-lambda.git
cd ruliad-lambda

# Build and verify
lake exe cache get  # Download Mathlib cache
lake build --wfail

# Run multiway demo
lake exe lambda_multiway_demo
```

## Module Structure

```
HeytingLean/LoF/Combinators/Lambda/
├── Syntax.lean       # de Bruijn Term type
├── ShiftSubst.lean   # Shift & substitution calculus
├── Beta.lean         # β-reduction, multiway edges
├── Confluence.lean   # Church-Rosser theorem
├── SKYBridge.lean    # λ ↔ SK translation
├── Enumeration.lean  # Term enumeration
└── Ruliology.lean    # Multiway exploration utilities
```

## Verification

```bash
./scripts/verify_build.sh
```

This checks:
- No `sorry`/`admit` in codebase
- Library builds with `--wfail`
- Executable compiles and runs

## Reference

Stephen Wolfram, "The Ruliology of Lambdas" (2025)
https://writings.stephenwolfram.com/2025/09/the-ruliology-of-lambdas/

## License

MIT License - see [LICENSE](LICENSE)
