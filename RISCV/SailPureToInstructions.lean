import RISCV.SailPure
import RISCV.Instructions

/-!
  Proofs of the equivalence between monad-free Sail specifications and bitvec-only semantics for
  RISCV operations.
-/

namespace RV64I

theorem add_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64I.addiw imm rs1_val = RV64I.addiw imm rs1_val := by
  simp only [SailRV64I.addiw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, Nat.sub_zero,
    Nat.reduceAdd, Sail.BitVec.extractLsb, RV64I.addiw, BitVec.add_eq]
  rw [BitVec.extractLsb, BitVec.setWidth_eq_extractLsb' (by omega)]
  unfold instHPowInt_leanRV64D
  bv_decide
