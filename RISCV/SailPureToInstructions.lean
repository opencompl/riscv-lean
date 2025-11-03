import RISCV.SailPure
import RISCV.Instructions
import RISCV.ForLean

/-!
  Proofs of the equivalence between monad-free Sail specifications and bitvec-only semantics for
  RISCV operations.
  Ordered as in https://docs.riscv.org/reference/isa/unpriv/rv64.html
-/

namespace RV64I

/-! # RV64I HINT -/

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
    SailRV64I.addiw imm rs1_val = RV64I.addiw imm rs1_val := by
  simp only [SailRV64I.addiw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, Nat.sub_zero,
    Nat.reduceAdd, Sail.BitVec.extractLsb, RV64I.addiw, BitVec.add_eq]
  rw [BitVec.extractLsb, BitVec.setWidth_eq_extractLsb' (by omega)]
  unfold instHPowInt_leanRV64D
  bv_decide

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

theorem rtype_add_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.ADD rs2_val rs1_val = RV64I.add rs2_val rs1_val := by rfl

theorem rtype_sub_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.SUB rs2_val rs1_val = RV64I.sub rs2_val rs1_val := by rfl

theorem rtype_sll_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.SLL rs2_val rs1_val = RV64I.sll rs2_val rs1_val := by rfl

theorem rtype_slt_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.SLT rs2_val rs1_val = RV64I.slt rs2_val rs1_val := by rfl

theorem rtype_sltu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.SLTU rs2_val rs1_val = RV64I.sltu rs2_val rs1_val := by rfl

theorem rtype_xor_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.XOR rs2_val rs1_val = RV64I.xor rs2_val rs1_val := by rfl

theorem rtype_srl_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.SRL rs2_val rs1_val = RV64I.srl rs2_val rs1_val := by rfl

theorem rtype_sra_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.SRA rs2_val rs1_val = RV64I.sra rs2_val rs1_val := by
  simp only [SailRV64I.rtype, Nat.sub_zero, sra, Nat.reduceAdd, BitVec.sshiftRight_eq',
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow,
    sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one]
  rfl

theorem rtype_or_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.OR rs2_val rs1_val = RV64I.or rs2_val rs1_val := by rfl

theorem rtype_and_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.AND rs2_val rs1_val = RV64I.and rs2_val rs1_val := by rfl

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

theorem shiftiwop_sraiw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64I.shiftiwop shamt sopw.SRAIW rs1_val = sraiw shamt rs1_val := by
  simp only [SailRV64I.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.shift_bits_right_arith, LeanRV64D.Functions.shift_right_arith,
    Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceSub, sraiw, Nat.sub_zero, Nat.reduceAdd,
    BitVec.sshiftRight_eq', sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one]
  rfl
theorem rtypew_addw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64I.rtypew ropw.ADDW rs1_val rs2_val = addw rs1_val rs2_val := by
  simp only [SailRV64I.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb, addw, BitVec.add_eq]
  rfl

theorem rtypew_subw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64I.rtypew ropw.SUBW rs1_val rs2_val = subw rs1_val rs2_val := by
  simp only [SailRV64I.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb, subw, BitVec.sub, Nat.reducePow,
    BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rfl

theorem rtypew_sllw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64I.rtypew ropw.SLLW rs1_val rs2_val = sllw rs1_val rs2_val := by
  simp only [SailRV64I.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb, sllw]
  rfl

theorem rtypew_srlw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64I.rtypew ropw.SRLW rs1_val rs2_val = srlw rs1_val rs2_val := by
  simp only [SailRV64I.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb, srlw]
  rfl

theorem rtypew_sraw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64I.rtypew ropw.SRAW rs1_val rs2_val = sraw rs1_val rs2_val := by
  simp only [SailRV64I.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.shift_bits_right_arith, Sail.BitVec.extractLsb, Nat.sub_zero, Nat.reduceAdd,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, Nat.reduceDvd, Nat.mod_mod_of_dvd,
    sraw, BitVec.sshiftRight_eq', sshiftRight_eq_setWidth_extractLsb_signExtend,
    Nat.add_one_sub_one]
  rfl

/-! # M Extension for Integer Multiplication and Division -/

theorem rem_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rem false rs1_val rs2_val = rem rs1_val rs2_val := by
  simp only [SailRV64I.rem, rem, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int,
    Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  rw [extractLsb'_ofInt_eq_ofInt (h := by simp)]
  by_cases h : rs1_val = 0#64
  · simp [h]
  · have h' := h
    simp only [← BitVec.toInt_inj, BitVec.toInt_zero] at h
    simp only [h, reduceIte, ← BitVec.toInt_inj, BitVec.toInt_srem, BitVec.ofInt_toInt_tmod_toInt]

theorem remu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rem true rs1_val rs2_val = remu rs1_val rs2_val := by
  simp only [SailRV64I.rem, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, remu]
  by_cases h1 : rs1_val = 0#64
  · simp [h1, BitVec.extractLsb'_setWidth_of_le]
  · simp only [Nat.reduceAdd, reduceIte, beq_iff_eq]
    have h1' : ¬rs1_val.toNat = 0 := by simp [BitVec.toNat_eq] at h1; exact h1
    simp only [Int.natCast_eq_zero, BitVec.umod_eq]
    rw [extractLsb'_ofInt_eq_ofInt (by omega)]
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_ofInt, Nat.reducePow, BitVec.toInt_umod, h1', reduceIte]
    congr

theorem remw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.remw False rs1_val rs2_val = remw rs1_val rs2_val := by
  simp only [SailRV64I.remw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd, decide_false,
    Bool.false_eq_true, reduceIte, Nat.reduceSub, Sail.BitVec.extractLsb, beq_iff_eq, remw]
  rw [extractLsb'_ofInt_eq_ofInt (h:= by simp)]
  split
  · case _ htrue =>
    have heq := BitVec.eq_of_toInt_eq (x := BitVec.extractLsb 31 0 rs1_val) (y := 0#64) htrue
    simp only [Nat.sub_zero, Nat.reduceAdd, Nat.reduceLeDiff, BitVec.setWidth_ofNat_of_le] at heq
    congr
    simp only [heq, BitVec.ofInt_toInt, BitVec.srem_zero]
  · case _ hfalse =>
    rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]
    congr

theorem remuw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.remw True rs1_val rs2_val = remuw rs1_val rs2_val := by
  simp only [SailRV64I.remw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd, Nat.reduceSub,
    Sail.BitVec.extractLsb, beq_iff_eq, remuw, decide_true, reduceIte, BitVec.umod_eq]
  rw [extractLsb'_ofInt_eq_ofInt (h:= by simp)]
  split
  · case _ htrue =>
    congr
    norm_cast at htrue
    have heq := BitVec.eq_of_toNat_eq (x := BitVec.extractLsb 31 0 rs1_val) (y := 0#32) htrue
    simp only [BitVec.ofInt_natCast, heq, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.umod_zero]
  · case _ hfalse =>
    congr
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.sub_zero, Nat.reduceAdd,
      Nat.reducePow, Int.natCast_emod, Int.cast_ofNat_Int, BitVec.toInt_ofInt, BitVec.toInt_umod]
    rfl
