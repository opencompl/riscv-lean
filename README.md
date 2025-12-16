# riscv-lean

Hand-polished, bitblastable semantics for RISC-V (RV64) in Lean 4, proven equivalent to the auto-generated authoritative semantics of the [Sail RISC-V model](https://github.com/opencompl/sail-riscv-lean).

## Supported Extensions

| Extension | Description | Status |
|-----------|-------------|--------|
| **RV64I** | Base Integer Instruction Set | ✅ |
| **M** | Integer Multiplication and Division | ✅ |
| **B - Zba** | Address generation | ✅ |
| **B - Zbb** | Basic bit-manipulation | ✅ |
| **B - Zbs** | Single-bit instructions | ✅ |
| **B - Zbkb** | Bit-manipulation for Cryptography | ✅ |
| **B - Zbc** | Carry-less multiplication | 🚧 |
| **B - Zbkc** | Carry-less multiplication for Cryptography | 🚧 |
| **B - Zbkx** | Crossbar permutations for Cryptography | 🚧 |

## Project Structure

| File | Description |
|------|-------------|
| `ForLean.lean` | Useful theorems to be upstreamed to Lean |
| `Instructions.lean` | Bitblasted RISC-V semantics |
| `SailPure.lean` | Purified (i.e., monad-free) Sail specifications |
| `SailPureToInstructions.lean` | Equivalence proofs between monad-free Sail specification and bitblastable RISC-V semantics |
| `SailToRV64.lean` | Equivalence proofs between monadic and monad-free Sail Specifications |
| `Skeleton.lean` | Core infrastructure and type definitions |

## Building

```bash
# Clone the repository
git clone https://github.com/opencompl/riscv-lean.git
cd riscv-lean

# Build the project
lake build
```

## Usage

Add `riscv-lean` as a dependency in your `lakefile.toml`:

```toml
[[require]]
name = "SailRV64"
git = "https://github.com/opencompl/riscv-lean"
rev = "main"
```

Then import the library in your Lean files:

```lean
import RISCV
```

## Development & Support
This project is developed and maintained by [Tobias Grosser](https://grosser.science), [Luisa Cicolini](https://github.com/luisacicolini), [Sarah Kuhn](https://www.linkedin.com/in/sarah-l-kuhn-9b64b1226/), and [Osman Yasar](https://www.linkedin.com/in/osman-yasar-577083162/) at the [University of Cambridge](https://cam.ac.uk/). 


## Related Projects

- [sail-riscv](https://github.com/riscv/sail-riscv) — Official Sail RISC-V specification
- [sail-riscv-lean](https://github.com/opencompl/sail-riscv-lean) — Auto-generated Lean 4 translation of the official Sail RISC-V model

