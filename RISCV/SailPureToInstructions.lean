import RISCV.SailPure
import RISCV.Instructions
import RISCV.ForLean

/-!
  Proofs of the equivalence between monad-free Sail specifications and bitvec-only semantics for
  RISCV operations.
-/

namespace RV64I

theorem utype_lui_eq (imm : BitVec 20) (pc : BitVec 64) :
    SailRV64I.utype imm pc (uop.LUI) = RV64I.lui imm pc := by
  simp only [SailRV64I.utype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    BitVec.signExtend, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, lui]
  unfold instHPowInt_leanRV64D
  bv_decide

theorem utype_auipc_eq (imm : BitVec 20) (pc : BitVec 64) :
    SailRV64I.utype imm pc (uop.AUIPC) = RV64I.auipc imm pc := by
  simp only [SailRV64I.utype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_eq, auipc, BitVec.append_eq]
  unfold instHPowInt_leanRV64D
  bv_decide

theorem addiw_eq (imm : BitVec 12) (rs1_val : BitVec 64) :

theorem shiftiop_slli_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.shiftiop shamt sop.SLLI rs1_val = slli shamt rs1_val := by
  simp [SailRV64I.shiftiop, Sail.shift_bits_left, slli]

theorem shiftiop_srli_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.shiftiop shamt sop.SRLI rs1_val = srli shamt rs1_val := by
  simp [SailRV64I.shiftiop, Sail.shift_bits_right, srli]

theorem shiftiop_srai_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.shiftiop shamt sop.SRAI rs1_val = srai shamt rs1_val := by
  simp only [SailRV64I.shiftiop, LeanRV64D.Functions.shift_bits_right_arith,
    LeanRV64D.Functions.shift_right_arith, Int.cast_ofNat_Int, Int.reduceSub,
    Sail.BitVec.extractLsb, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, srai,
    BitVec.sshiftRight_eq', sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one,
    BitVec.signExtend_eq]
  rfl

theorem shiftiwop_slliw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64I.shiftiwop shamt sopw.SLLIW rs1_val = slliw shamt rs1_val := by
  simp only [SailRV64I.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Sail.shift_bits_left, Sail.BitVec.extractLsb, slliw]
  unfold instHPowInt_leanRV64D
  bv_decide

theorem shiftiwop_srliw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64I.shiftiwop shamt sopw.SRLIW rs1_val = srliw shamt rs1_val := by
  simp only [SailRV64I.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Sail.shift_bits_right, Sail.BitVec.extractLsb, srliw]
  unfold instHPowInt_leanRV64D
  bv_decide


theorem sshiftRight_eq_setWidth_extractLsb_signExtend {w : Nat} (n : Nat) (x : BitVec w) :
    x.sshiftRight n = ((x.signExtend (w + n)).extractLsb (w - 1 + n) n).setWidth w := by
  ext i hi
  simp [BitVec.getElem_sshiftRight]
  simp [show i ≤ w - 1 by omega]
  simp [BitVec.getLsbD_signExtend]
  by_cases hni : (n + i) < w <;> simp [hni] <;> omega

theorem shiftiwop_sraiw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64I.shiftiwop shamt sopw.SRAIW rs1_val = sraiw shamt rs1_val := by
  simp only [SailRV64I.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.shift_bits_right_arith, LeanRV64D.Functions.shift_right_arith,
    Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceSub, sraiw, Nat.sub_zero, Nat.reduceAdd,
    BitVec.sshiftRight_eq', sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one]
  rfl

theorem shiftiop_slli_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.shiftiop shamt sop.SLLI rs1_val = slli shamt rs1_val := by
  simp [SailRV64I.shiftiop, Sail.shift_bits_left, slli]

theorem shiftiop_srli_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.shiftiop shamt sop.SRLI rs1_val = srli shamt rs1_val := by
  simp [SailRV64I.shiftiop, Sail.shift_bits_right, srli]

theorem shiftiop_srai_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.shiftiop shamt sop.SRAI rs1_val = srai shamt rs1_val := by
  simp only [SailRV64I.shiftiop, LeanRV64D.Functions.shift_bits_right_arith,
    LeanRV64D.Functions.shift_right_arith, Int.cast_ofNat_Int, Int.reduceSub,
    Sail.BitVec.extractLsb, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, srai,
    BitVec.sshiftRight_eq', sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one,
    BitVec.signExtend_eq]
  rfl
