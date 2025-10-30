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

theorem lui_eq (imm : BitVec 20) (pc : BitVec 64) :
    SailRV64I.utype imm pc (uop.LUI) = RV64I.lui imm pc := by
  simp only [SailRV64I.utype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    BitVec.signExtend, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, lui]
  unfold instHPowInt_leanRV64D
  bv_decide

theorem auipc_eq (imm : BitVec 20) (pc : BitVec 64) :
    SailRV64I.utype imm pc (uop.AUIPC)
    = RV64I.auipc imm pc:= by
  simp only [SailRV64I.utype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_eq, auipc, BitVec.append_eq]
  unfold instHPowInt_leanRV64D
  bv_decide
