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

## Visualizations

<table>
<tr>
<td align="center">
<a href="https://abraxas1010.github.io/ruliad-lambda/visualizations/church_rosser_diamond.svg">
<img src="visualizations/church_rosser_diamond.svg" width="280" alt="Church-Rosser Diamond"/>
</a>
<br/><b>Church-Rosser Confluence</b>
</td>
<td align="center">
<a href="https://abraxas1010.github.io/ruliad-lambda/visualizations/multiway_confluence.svg">
<img src="visualizations/multiway_confluence.svg" width="280" alt="Multiway Confluence"/>
</a>
<br/><b>Multiway β-Reduction</b>
</td>
</tr>
<tr>
<td align="center">
<a href="https://abraxas1010.github.io/ruliad-lambda/visualizations/multiway_size6.svg">
<img src="visualizations/multiway_size6.svg" width="280" alt="Size-6 Multiway"/>
</a>
<br/><b>Size-6 Term Graph</b>
</td>
<td align="center">
<a href="https://abraxas1010.github.io/ruliad-lambda/visualizations/ruliad_branchial.svg">
<img src="visualizations/ruliad_branchial.svg" width="280" alt="Branchial Graph"/>
</a>
<br/><b>Branchial Structure</b>
</td>
</tr>
</table>

### Interactive Visualizations

- **[Proof Dependency Graph (3D)](https://abraxas1010.github.io/ruliad-lambda/visualizations/proof_dependencies.html)** — Interactive 3D view of theorem dependencies
- **[Lambda Multiway Explorer](https://abraxas1010.github.io/ruliad-lambda/visualizations/ruliad_lambda_3d.html)** — 3D term visualization

*Neon purple Ruliad palette: `#9D4EDD` `#7B2CBF` `#E0AAFF` `#10002B`*

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

## Documentation

- **[Claims & Proofs](docs/CLAIMS_AND_PROOFS.md)** — Mapping Wolfram's claims to Lean theorems
- **[Notebook-Style Narrative](docs/NOTEBOOK_STYLE_README.md)** — Computational essay with full visualizations

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
