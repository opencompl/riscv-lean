import RISCV.SailPure
import RISCV.Instructions
import RISCV.ForLean
import LeanRV64D.Arithmetic

/-!
  Proofs of the equivalence between monad-free Sail specifications and bitvec-only semantics for
  RISCV operations.
  Ordered as in https://docs.riscv.org/reference/isa/unpriv/rv64.html
-/

namespace RV64

/-! # RV64I Base Integer Instruction Set -/

theorem utype_lui_eq (imm : BitVec 20) (pc : BitVec 64) :
    SailRV64.utype imm pc (uop.LUI) = lui imm := by
  simp [SailRV64.utype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, lui]

theorem utype_auipc_eq (imm : BitVec 20) (pc : BitVec 64) :
    SailRV64.utype imm pc (uop.AUIPC) = auipc imm pc := by
  simp [SailRV64.utype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, auipc, BitVec.add_comm]

theorem itype_addi_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64.itype imm rs1_val iop.ADDI = addi imm rs1_val := by
  simp [SailRV64.itype, addi, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]

theorem itype_slti_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64.itype imm rs1_val iop.SLTI = slti imm rs1_val := by
  simp [SailRV64.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, LeanRV64D.Functions.zero_extend, LeanRV64D.Functions.bool_to_bits, Sail.BitVec.zeroExtend, LeanRV64D.Functions.bool_bits_forwards, LeanRV64D.Functions.zopz0zI_s, slti]
  split <;>
  case _ arg h =>
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.slt, h]

theorem itype_sltiu_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64.itype imm rs1_val iop.SLTIU = sltiu imm rs1_val := by
  simp [SailRV64.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, LeanRV64D.Functions.zero_extend, LeanRV64D.Functions.bool_to_bits, Sail.BitVec.zeroExtend, LeanRV64D.Functions.bool_bits_forwards, LeanRV64D.Functions.zopz0zI_u, sltiu, Sail.BitVec.toNatInt]
  split <;>
  case _ arg h =>
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.ult, h]

theorem itype_andi_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64.itype imm rs1_val iop.ANDI = andi imm rs1_val := by
  simp [SailRV64.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, andi]

theorem itype_ori_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64.itype imm rs1_val iop.ORI = ori imm rs1_val := by
  simp [SailRV64.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, ori]

theorem itype_xori_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64.itype imm rs1_val iop.XORI = xori imm rs1_val := by
  simp [SailRV64.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, xori]

theorem addiw_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64.addiw imm rs1_val = addiw imm rs1_val := by
  simp only [SailRV64.addiw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, Nat.sub_zero,
    Nat.reduceAdd, Sail.BitVec.extractLsb, addiw]
  rw [BitVec.extractLsb, BitVec.setWidth_eq_extractLsb' (by omega)]
  unfold instHPowInt_leanRV64D
  bv_decide

theorem shiftiop_slli_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64.shiftiop shamt sop.SLLI rs1_val = slli shamt rs1_val := by
  simp [SailRV64.shiftiop, Sail.shift_bits_left, slli]

theorem shiftiop_srli_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64.shiftiop shamt sop.SRLI rs1_val = srli shamt rs1_val := by
  simp [SailRV64.shiftiop, Sail.shift_bits_right, srli]

theorem shiftiop_srai_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64.shiftiop shamt sop.SRAI rs1_val = srai shamt rs1_val := by
  simp only [SailRV64.shiftiop, LeanRV64D.Functions.shift_bits_right_arith,
    LeanRV64D.Functions.shift_right_arith, Int.cast_ofNat_Int, Int.reduceSub,
    Sail.BitVec.extractLsb, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, srai,
    BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one,
    BitVec.signExtend_eq]
  rfl

theorem rtype_add_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.ADD rs2_val rs1_val = add rs2_val rs1_val := by rfl

theorem rtype_sub_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.SUB rs2_val rs1_val = sub rs2_val rs1_val := by rfl

theorem rtype_sll_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.SLL rs2_val rs1_val = sll rs2_val rs1_val := by rfl

theorem rtype_slt_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.SLT rs2_val rs1_val = slt rs2_val rs1_val := by rfl

theorem rtype_sltu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.SLTU rs2_val rs1_val = sltu rs2_val rs1_val := by
  simp [SailRV64.rtype, sltu]
  simp [LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend, LeanRV64D.Functions.bool_to_bits,
    Sail.BitVec.toNatInt, LeanRV64D.Functions.bool_bits_forwards, LeanRV64D.Functions.zopz0zI_u]
  by_cases h : rs1_val.toNat < rs2_val.toNat <;>
  simp [h, BitVec.ult]

theorem rtype_xor_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.XOR rs2_val rs1_val = xor rs2_val rs1_val := by rfl

theorem rtype_srl_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.SRL rs2_val rs1_val = srl rs2_val rs1_val := by rfl

theorem rtype_sra_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.SRA rs2_val rs1_val = sra rs2_val rs1_val := by
  simp only [SailRV64.rtype, Nat.sub_zero, sra, Nat.reduceAdd, BitVec.sshiftRight_eq',
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow,
    BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one]
  rfl

theorem rtype_or_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.OR rs2_val rs1_val = or rs2_val rs1_val := by rfl

theorem rtype_and_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rtype rop.AND rs2_val rs1_val = and rs2_val rs1_val := by rfl

theorem shiftiwop_slliw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64.shiftiwop shamt sopw.SLLIW rs1_val = slliw shamt rs1_val := by
  simp [SailRV64.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Sail.shift_bits_left, Sail.BitVec.extractLsb, slliw, BitVec.extractLsb'_eq_extractLsb,
    Nat.mod_eq_of_lt (a := shamt.toNat) (b := 64) (by omega)]

theorem shiftiwop_srliw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64.shiftiwop shamt sopw.SRLIW rs1_val = srliw shamt rs1_val := by
  simp [SailRV64.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Sail.shift_bits_right, Sail.BitVec.extractLsb, srliw, BitVec.extractLsb'_eq_extractLsb,
    Nat.mod_eq_of_lt (a := shamt.toNat) (b := 64) (by omega)]

theorem shiftiwop_sraiw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64.shiftiwop shamt sopw.SRAIW rs1_val = sraiw shamt rs1_val := by
  simp only [SailRV64.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.shift_bits_right_arith, LeanRV64D.Functions.shift_right_arith,
    Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceSub, sraiw, Nat.sub_zero, Nat.reduceAdd,
    BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one]
  rfl
theorem rtypew_addw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64.rtypew ropw.ADDW rs1_val rs2_val = addw rs1_val rs2_val := by
  simp only [SailRV64.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb, addw, BitVec.add_eq]
  rfl

theorem rtypew_subw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64.rtypew ropw.SUBW rs1_val rs2_val = subw rs1_val rs2_val := by
  simp only [SailRV64.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb, subw, BitVec.sub, Nat.reducePow,
    BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rfl

theorem rtypew_sllw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64.rtypew ropw.SLLW rs1_val rs2_val = sllw rs1_val rs2_val := by
  simp only [SailRV64.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb, sllw]
  rfl

theorem rtypew_srlw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64.rtypew ropw.SRLW rs1_val rs2_val = srlw rs1_val rs2_val := by
  simp only [SailRV64.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb, srlw]
  rfl

theorem rtypew_sraw_eq (rs1_val : BitVec 64) (rs2_val : BitVec 64) :
    SailRV64.rtypew ropw.SRAW rs1_val rs2_val = sraw rs1_val rs2_val := by
  simp only [SailRV64.rtypew, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.shift_bits_right_arith, Sail.BitVec.extractLsb, Nat.sub_zero, Nat.reduceAdd,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, Nat.reduceDvd, Nat.mod_mod_of_dvd,
    sraw, BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend,
    Nat.add_one_sub_one, Sail.BitVec.toNatInt]
  rfl

/-! # M Extension for Integer Multiplication and Division -/

theorem rem_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rem false rs1_val rs2_val = rem rs1_val rs2_val := by
  simp only [SailRV64.rem, rem, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int,
    Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (h := by simp)]
  by_cases h : rs1_val = 0#64
  · simp [h]
  · have h' := h
    simp only [← BitVec.toInt_inj, BitVec.toInt_zero] at h
    simp only [h, reduceIte, ← BitVec.toInt_inj, BitVec.toInt_srem, BitVec.ofInt_toInt_tmod_toInt]

theorem remu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rem true rs1_val rs2_val = remu rs1_val rs2_val := by
  simp only [SailRV64.rem, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, remu]
  by_cases h1 : rs1_val = 0#64
  · simp [h1, BitVec.extractLsb'_setWidth_of_le]
  · simp only [Nat.reduceAdd, reduceIte, beq_iff_eq]
    have h1' : ¬rs1_val.toNat = 0 := by simp [BitVec.toNat_eq] at h1; exact h1
    simp only [Int.natCast_eq_zero, BitVec.umod_eq]
    rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_ofInt, Nat.reducePow, BitVec.toInt_umod, h1', reduceIte]
    congr

theorem remw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.remw False rs1_val rs2_val = remw rs1_val rs2_val := by
  simp only [SailRV64.remw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd, decide_false,
    Bool.false_eq_true, reduceIte, Nat.reduceSub, Sail.BitVec.extractLsb, beq_iff_eq, remw]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (h:= by simp)]
  split
  · case _ htrue =>
    have heq := BitVec.eq_of_toInt_eq (x := BitVec.extractLsb 31 0 rs1_val) (y := 0#64) htrue
    simp only [Nat.sub_zero, Nat.reduceAdd, Nat.reduceLeDiff, BitVec.setWidth_ofNat_of_le] at heq
    congr
    simp only [heq, BitVec.ofInt_toInt, BitVec.srem_zero]
  · case _ hfalse =>
    rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem remuw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.remw True rs1_val rs2_val = remuw rs1_val rs2_val := by
  simp only [SailRV64.remw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd, Nat.reduceSub,
    Sail.BitVec.extractLsb, beq_iff_eq, remuw, decide_true, reduceIte, BitVec.umod_eq]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (h:= by simp)]
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

theorem mul_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mul rs1_val rs2_val {result_part := VectorHalf.Low, signed_rs1 := Signedness.Signed, signed_rs2 := Signedness.Signed} =
      mul rs1_val rs2_val := by
  have h1: rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  have h2 : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp [SailRV64.mul, LeanRV64D.Functions.mult_to_bits_half, Sail.BitVec.extractLsb,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, mul, BitVec.extractLsb,
    h2, h1, BitVec.ofInt_mul, BitVec.extractLsb'_eq_setWidth, BitVec.setWidth_mul,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_signExtend_eq_self, BitVec.mul_comm]

theorem mulh_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mul rs1_val rs2_val {result_part := VectorHalf.High, signed_rs1 := Signedness.Signed, signed_rs2 := Signedness.Signed} =
      mulh rs1_val rs2_val := by
  have h1 : rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  have h2 : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp only [SailRV64.mul, LeanRV64D.Functions.mult_to_bits_half, Int.cast_ofNat_Int,
    Int.reduceMul, Int.reduceSub, Int.reduceToNat, Nat.reduceSub, Nat.reduceAdd,
    Sail.BitVec.extractLsb, BitVec.extractLsb, LeanRV64D.Functions.to_bits_truncate,
    Sail.get_slice_int, h2, h1, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.extractLsb'_eq_setWidth, mulh]
  rw [BitVec.extractLsb'_setWidth_of_le (by omega), BitVec.setWidth_eq_extractLsb' (by omega)]
  simp

theorem mulhu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mul rs1_val rs2_val {result_part := VectorHalf.High, signed_rs1 := Signedness.Unsigned, signed_rs2 := Signedness.Unsigned} =
      mulhu rs1_val rs2_val := by
    simp only [SailRV64.mul, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.cast_ofNat_Int,
      Int.reduceMul, Int.reduceToNat, Int.reduceSub, Nat.reduceSub, Nat.reduceAdd,
      LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, mulhu, BitVec.truncate_eq_setWidth,
      BitVec.extractLsb'_eq_self, LeanRV64D.Functions.mult_to_bits_half]
    rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
    congr

theorem mulhsu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mul rs1_val rs2_val {result_part := VectorHalf.High, signed_rs1 := Signedness.Signed, signed_rs2 := Signedness.Unsigned} =
      mulhsu rs1_val rs2_val := by
  simp [SailRV64.mul, LeanRV64D.Functions.mult_to_bits_half, Sail.BitVec.extractLsb,
    Int.cast_ofNat_Int, Int.reduceMul, Int.reduceToNat, Int.reduceSub,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    mulhsu, BitVec.truncate_eq_setWidth, Sail.BitVec.toNatInt]
  have h1 : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
      simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  have h2 : rs1_val.toNat = (rs1_val.zeroExtend 129).toInt := by
      simp only [BitVec.truncate_eq_setWidth, BitVec.toInt_setWidth]
      rw [Int.bmod_eq_of_le (n := (rs1_val.toNat : Int)) (by omega) (by omega)]
      simp
  simp only [h1, h2]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toInt_setWidth, Nat.reducePow, BitVec.ofInt_mul,
    BitVec.ofInt_toInt]
  rw [Int.bmod_eq_of_le (n := (rs1_val.toNat : Int)) (by omega) (by omega), BitVec.ofInt_natCast,
    BitVec.extractLsb'_eq_setWidth, BitVec.extractLsb_setWidth_of_lt]
  simp only [Int.toNat_natCast, BitVec.ofNat_toNat]
  · omega
  · omega

theorem mulw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mulw rs1_val rs2_val = mulw rs1_val rs2_val := by
  simp only [SailRV64.mulw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Sail.BitVec.extractLsb, mulw]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (h := by simp), BitVec.extractLsb]
  congr
  apply BitVec.eq_of_toInt_eq
  simp

theorem div_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.div rs1_val rs2_val False = div rs1_val rs2_val := by
  simp only [SailRV64.div, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    LeanRV64D.Functions.not, decide_false, Bool.not_false, Bool.false_eq_true, reduceIte,
    beq_iff_eq, Int.reduceNeg, LeanRV64D.Functions.xlen, Int.cast_ofNat_Int, Int.reduceSub,
    ge_iff_le, Bool.true_and, decide_eq_true_eq, div]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  by_cases h1 : rs1_val = 0#64
  · case pos =>
    simp [h1, show ¬ (2 ^ (63 : Int) : Int) ≤ -1 by omega]
  · case neg =>
    have h1' : ¬ rs1_val.toInt = 0 := (BitVec.toInt_ne).mpr h1
    simp only [h1', reduceIte, h1]
    apply BitVec.eq_of_toInt_eq
    by_cases hcond : rs2_val ≠ BitVec.intMin 64 ∨ rs1_val ≠ -1#64
    · rw [← BitVec.toInt_sdiv_of_ne_or_ne rs2_val rs1_val hcond]
      split
      · have := BitVec.toInt_le (x := rs2_val.sdiv rs1_val)
        omega
      · simp
    · simp only [ne_eq, not_or, Decidable.not_not] at hcond
      obtain ⟨hcond, hcond'⟩ := hcond
      simp only [hcond, BitVec.toInt_intMin, Nat.add_one_sub_one, Nat.reducePow, Nat.reduceMod,
        Int.cast_ofNat_Int, Int.reduceNeg, hcond', BitVec.reduceNeg, BitVec.reduceToInt,
        Int.tdiv_neg, Int.tdiv_one, Int.neg_neg, BitVec.toInt_ofInt]
      rw [Int.bmod_eq_of_le (by omega) (by omega)]
      rfl

theorem divw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.divw rs1_val rs2_val False = divw rs1_val rs2_val := by
  simp only [SailRV64.divw, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    LeanRV64D.Functions.not, decide_false, Bool.not_false, Bool.false_eq_true, reduceIte,
    beq_iff_eq, Int.reduceNeg, ge_iff_le, Bool.true_and, decide_eq_true_eq, divw,
    LeanRV64D.Functions.sign_extend, Sail.BitVec.extractLsb, Sail.BitVec.signExtend]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  by_cases h1 : BitVec.extractLsb 31 0 rs1_val = 0#32
  · case pos =>
    simp [h1, show ¬ (2 ^ (31 : Int) : Int) ≤ -1 by omega]
  · case neg =>
    generalize hrs1 : (BitVec.extractLsb 31 0 rs1_val) = rs1 at *
    generalize hrs2 : (BitVec.extractLsb 31 0 rs2_val) = rs2 at *
    have h1' : ¬ rs1.toInt = 0 := (BitVec.toInt_ne).mpr h1
    simp only [h1', reduceIte, h1]
    apply BitVec.eq_of_toInt_eq
    by_cases hcond : rs2 ≠ BitVec.intMin 32 ∨ rs1 ≠ -1#32
    · rw [← BitVec.toInt_sdiv_of_ne_or_ne rs2 rs1 hcond]
      split
      · have := BitVec.toInt_le (x := rs2.sdiv rs1)
        omega
      · simp
    · simp only [ne_eq, not_or, Decidable.not_not] at hcond
      obtain ⟨hcond, hcond'⟩ := hcond
      congr
      simp only [Nat.sub_zero, Nat.reduceAdd, hcond, BitVec.toInt_intMin, Nat.add_one_sub_one,
        hcond', BitVec.reduceNeg, BitVec.reduceToInt, Int.tdiv_neg, Int.tdiv_one, Int.neg_neg,
        Nat.mod_eq_of_lt (a := 2^31) (b := 2^32) (by omega),
        show (2 ^ (31 : Int) : Int) ≤ (2 ^ (31 : Nat) : Nat) by omega]
      rfl

theorem divu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.div rs1_val rs2_val True = divu rs1_val rs2_val := by
  simp only [SailRV64.div, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    LeanRV64D.Functions.not, decide_true, Bool.not_true, ↓reduceIte, beq_iff_eq,
    Int.natCast_eq_zero, LeanRV64D.Functions.xlen, ge_iff_le, Bool.false_and, Bool.false_eq_true,
    divu, BitVec.ofNat_eq_ofNat, BitVec.udiv_eq]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  split
  · case _ heq =>
    rw [show 0 = (0#64).toNat by rfl, ← BitVec.toNat_eq] at heq
    simp [heq]
  · case _ hne =>
    rw [show 0 = (0#64).toNat by rfl, ← BitVec.toNat_eq] at hne
    simp only [hne, reduceIte, ← Int.ofNat_tdiv, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    have := Nat.div_lt_of_lt (a := rs2_val.toNat) (b := rs1_val.toNat) (c := 2 ^ 64) (by omega)
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := rs2_val.toNat / rs1_val.toNat) (b := 2 ^ 64) (by omega)]

theorem divuw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.divw rs1_val rs2_val True = divuw rs1_val rs2_val := by
  simp only [SailRV64.divw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    LeanRV64D.Functions.not, decide_true, Bool.not_true, ↓reduceIte, Sail.BitVec.extractLsb,
    beq_iff_eq, Int.natCast_eq_zero, ge_iff_le, Bool.false_and, Bool.false_eq_true, divuw,
    BitVec.udiv_eq]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  split
  · case _ heq =>
    rw [show ((BitVec.extractLsb 31 0 rs1_val).toNat = 0) =
        ((BitVec.extractLsb 31 0 rs1_val).toNat = (0#(31 - 0 + 1)).toNat) by rfl, ← BitVec.toNat_eq] at heq
    simp [heq]
  · case _ hne =>
    rw [show ((BitVec.extractLsb 31 0 rs1_val).toNat = 0) =
        ((BitVec.extractLsb 31 0 rs1_val).toNat = (0#(31 - 0 + 1)).toNat) by rfl, ← BitVec.toNat_eq] at hne
    generalize hrs1 : (BitVec.extractLsb 31 0 rs1_val) = rs1 at *
    generalize hrs2 : (BitVec.extractLsb 31 0 rs2_val) = rs2 at *
    congr
    simp only [hne, reduceIte, ← Int.ofNat_tdiv, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    have := Nat.div_lt_of_lt (a := rs2.toNat) (b := rs1.toNat) (c := 2 ^ 32) (by omega)
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := rs2.toNat / rs1.toNat) (b := 2 ^ 32) (by omega)]

/-! # "B" Extension for Bit Manipulation -/

/-! ## Zba: Address generation -/

theorem zba_rtypeuw_adduw (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zba_rtypeuw rs2_val rs1_val 0#2 = adduw rs2_val rs1_val := by
  simp [SailRV64.zba_rtypeuw, adduw, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.extractLsb,
    Sail.BitVec.zeroExtend]

theorem zba_rtypeuw_sh1adduw (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zba_rtypeuw rs2_val rs1_val 1#2 = sh1adduw rs2_val rs1_val := by
  simp [SailRV64.zba_rtypeuw, sh1adduw, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.extractLsb,
    Sail.BitVec.zeroExtend]

theorem zba_rtypeuw_sh2adduw (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zba_rtypeuw rs2_val rs1_val 2#2 = sh2adduw rs2_val rs1_val := by
  simp [SailRV64.zba_rtypeuw, sh2adduw, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.extractLsb,
    Sail.BitVec.zeroExtend]

theorem zba_rtypeuw_sh3adduw (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zba_rtypeuw rs2_val rs1_val 3#2 = sh3adduw rs2_val rs1_val := by
  simp [SailRV64.zba_rtypeuw, sh3adduw, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.extractLsb,
    Sail.BitVec.zeroExtend]

theorem zba_rtypeuw_sh1add (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zba_rtype rs2_val rs1_val 1#2 = sh1add rs2_val rs1_val := by
  simp [SailRV64.zba_rtype, sh1add, Sail.shift_bits_left]

theorem zba_rtype_sh2add (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zba_rtype rs2_val rs1_val 2#2 = sh2add rs2_val rs1_val := by
  simp [SailRV64.zba_rtype, sh2add, Sail.shift_bits_left]

theorem zba_rtype_sh3add (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zba_rtype rs2_val rs1_val 3#2 = sh3add rs2_val rs1_val := by
  simp [SailRV64.zba_rtype, sh3add, Sail.shift_bits_left]

theorem zba_rtypew_slliuw (rs1_val : BitVec 64) (shamt : BitVec 6) :
    SailRV64.zba_slliuw shamt rs1_val = slliuw shamt rs1_val := by
  simp [SailRV64.zba_slliuw, slliuw, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend,
    Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]

/-! ## Zbb: Basic bit-manipulation -/

theorem zbb_rtype_andn_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtype rs1_val rs2_val brop_zbb.ANDN  = andn rs1_val rs2_val := by
  simp [SailRV64.zbb_rtype, andn]

theorem zbb_rtype_orn_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtype rs1_val rs2_val brop_zbb.ORN  = orn rs1_val rs2_val := by
  simp [SailRV64.zbb_rtype, orn]

theorem zbb_rtype_xorn_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtype rs1_val rs2_val brop_zbb.XNOR  = xnor rs1_val rs2_val := by
  simp [SailRV64.zbb_rtype, xnor]

theorem zbb_rtype_max_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtype rs1_val rs2_val brop_zbb.MAX  = max rs1_val rs2_val := by
  simp [SailRV64.zbb_rtype, max, LeanRV64D.Functions.zopz0zK_s, BitVec.slt]

theorem zbb_rtype_maxu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtype rs1_val rs2_val brop_zbb.MAXU  = maxu rs1_val rs2_val := by
  simp [SailRV64.zbb_rtype, maxu, LeanRV64D.Functions.zopz0zK_u, BitVec.ult, Sail.BitVec.toNatInt]

theorem zbb_rtype_min_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtype rs1_val rs2_val brop_zbb.MIN  = min rs1_val rs2_val := by
  simp [SailRV64.zbb_rtype, min, LeanRV64D.Functions.zopz0zI_s, BitVec.slt]

theorem zbb_rtype_minu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtype rs1_val rs2_val brop_zbb.MINU  = minu rs1_val rs2_val := by
  simp [SailRV64.zbb_rtype, minu, LeanRV64D.Functions.zopz0zI_u, BitVec.ult, Sail.BitVec.toNatInt]

theorem zbb_rtype_rol_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtype rs1_val rs2_val brop_zbb.ROL  = rol rs1_val rs2_val := by
  simp only [SailRV64.zbb_rtype, LeanRV64D.Functions.rotate_bits_left, LeanRV64D.Functions.rotatel,
    Sail.shiftl, Sail.BitVec.toNatInt, Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, Sail.shiftr, Sail.BitVec.length,
    rol, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  by_cases hzero : rs1_val.toNat % 64 = 0
  · simp only [hzero, Int.ofNat_eq_coe, Int.cast_ofNat_Int, Int.toNat_zero, BitVec.shiftLeft_zero,
      Int.sub_zero, Int.reduceToNat, BitVec.reduceOfNat, BitVec.zero_sub, BitVec.toNat_neg,
      Nat.reducePow, BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.sub_zero, Nat.reduceAdd,
      Nat.mod_self, BitVec.ushiftRight_zero, BitVec.or_self]
    have hzero' : rs2_val >>> 64 = 0#64 := by
      ext i hi
      simp
    simp [hzero']
  · have : (64#6 - BitVec.extractLsb 5 0 rs1_val).toNat = ((64 : Int) - (Int.ofNat (rs1_val.toNat % 64)).toNat).toNat := by
      have : (64 - ((Int.ofNat (rs1_val.toNat % 64)).toNat : Int)).toNat = 64 - (Int.ofNat (rs1_val.toNat % 64)).toNat := by
        simp only [Int.ofNat_eq_coe, Int.natCast_emod, Int.cast_ofNat_Int, Int.ofNat_toNat]
        omega
      simp only [this]
      simp
      omega
    rw [this]
    congr

theorem zbb_rtype_ror_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtype rs1_val rs2_val brop_zbb.ROR  = ror rs1_val rs2_val := by
  simp only [SailRV64.zbb_rtype, LeanRV64D.Functions.rotate_bits_right, LeanRV64D.Functions.rotater,
    Sail.shiftr, Sail.BitVec.toNatInt, Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, Sail.shiftl, Sail.BitVec.length,
    ror, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  by_cases hzero : rs1_val.toNat % 64 = 0
  · simp [hzero]
  · have : (64#6 - BitVec.extractLsb 5 0 rs1_val).toNat = ((64 : Int) - (Int.ofNat (rs1_val.toNat % 64)).toNat).toNat := by
      have : (64 - ((Int.ofNat (rs1_val.toNat % 64)).toNat : Int)).toNat = 64 - (Int.ofNat (rs1_val.toNat % 64)).toNat := by
        simp only [Int.ofNat_eq_coe, Int.natCast_emod, Int.cast_ofNat_Int, Int.ofNat_toNat]
        omega
      simp only [this]
      simp
      omega
    rw [this]
    congr

theorem zbb_rtypew_rolw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtypew rs1_val rs2_val bropw_zbb.ROLW  = rolw rs1_val rs2_val := by
  simp only [SailRV64.zbb_rtypew, LeanRV64D.Functions.rotate_bits_left, LeanRV64D.Functions.rotatel,
    Sail.shiftl, Sail.BitVec.toNatInt, Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, Sail.shiftr, Sail.BitVec.length,
    rolw, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  by_cases hzero : rs1_val.toNat % 32 = 0
  · simp only [hzero, Int.ofNat_eq_coe, Int.cast_ofNat_Int, Int.toNat_zero, BitVec.shiftLeft_zero,
      Int.sub_zero, Int.reduceToNat, BitVec.signExtend_or, BitVec.reduceOfNat, BitVec.zero_sub,
      BitVec.toNat_neg, Nat.reducePow, BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.sub_zero,
      Nat.reduceAdd, Nat.mod_self, BitVec.ushiftRight_zero, BitVec.or_self]
    have : BitVec.setWidth 32 rs2_val >>> 32 = 0#32 := by
      ext i hi
      simp
    simp [this, BitVec.extractLsb, BitVec.extractLsb'_eq_setWidth]
  · have : (32#5 - BitVec.extractLsb 5 0 rs1_val).toNat = ((32 : Int) - (Int.ofNat (rs1_val.toNat % 32)).toNat).toNat := by
      have : (32 - ((Int.ofNat (rs1_val.toNat % 32)).toNat : Int)).toNat = 32 - (Int.ofNat (rs1_val.toNat % 32)).toNat := by
        simp only [Int.ofNat_eq_coe, Int.natCast_emod, Int.cast_ofNat_Int, Int.ofNat_toNat]
        omega
      simp only [this]
      simp
      omega
    congr
    simp only [BitVec.reduceOfNat, Nat.sub_zero, Nat.reduceAdd, BitVec.extractLsb,
      BitVec.extractLsb'_eq_setWidth, Nat.reduceLeDiff, BitVec.setWidth_setWidth_of_le,
      BitVec.zero_sub, BitVec.toNat_neg, Nat.reducePow, BitVec.toNat_setWidth, Int.ofNat_eq_coe,
      Int.natCast_emod, Int.cast_ofNat_Int, Int.ofNat_toNat] at this
    simp [BitVec.extractLsb, BitVec.extractLsb'_eq_setWidth, this]

theorem zbb_rtypew_rorw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbb_rtypew rs1_val rs2_val bropw_zbb.RORW  = rorw rs1_val rs2_val := by
  simp only [SailRV64.zbb_rtypew, LeanRV64D.Functions.rotate_bits_right, LeanRV64D.Functions.rotater,
    Sail.shiftl, Sail.BitVec.toNatInt, Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, Sail.shiftr, Sail.BitVec.length,
    rorw, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  by_cases hzero : rs1_val.toNat % 32 = 0
  · simp [hzero, BitVec.extractLsb, BitVec.extractLsb'_eq_setWidth]
  · have : (32#5 - BitVec.extractLsb 5 0 rs1_val).toNat = ((32 : Int) - (Int.ofNat (rs1_val.toNat % 32)).toNat).toNat := by
      have : (32 - ((Int.ofNat (rs1_val.toNat % 32)).toNat : Int)).toNat = 32 - (Int.ofNat (rs1_val.toNat % 32)).toNat := by
        simp only [Int.ofNat_eq_coe, Int.natCast_emod, Int.cast_ofNat_Int, Int.ofNat_toNat]
        omega
      simp only [this]
      simp
      omega
    congr
    simp only [BitVec.reduceOfNat, Nat.sub_zero, Nat.reduceAdd, BitVec.extractLsb,
      BitVec.extractLsb'_eq_setWidth, Nat.reduceLeDiff, BitVec.setWidth_setWidth_of_le,
      BitVec.zero_sub, BitVec.toNat_neg, Nat.reducePow, BitVec.toNat_setWidth, Int.ofNat_eq_coe,
      Int.natCast_emod, Int.cast_ofNat_Int, Int.ofNat_toNat] at this
    simp [BitVec.extractLsb, BitVec.extractLsb'_eq_setWidth, this]

theorem zbb_extop_sextb_eq (rs1_val : BitVec 64) :
    SailRV64.zbb_extop rs1_val extop_zbb.SEXTB  = sextb rs1_val := by
  simp [SailRV64.zbb_extop, sextb, LeanRV64D.Functions.sign_extend, Sail.BitVec.extractLsb, Sail.BitVec.signExtend]

theorem zbb_extop_sexth_eq (rs1_val : BitVec 64) :
    SailRV64.zbb_extop rs1_val extop_zbb.SEXTH  = sexth rs1_val := by
  simp [SailRV64.zbb_extop, sexth, LeanRV64D.Functions.sign_extend, Sail.BitVec.extractLsb, Sail.BitVec.signExtend]

theorem zbb_extop_zexth_eq (rs1_val : BitVec 64) :
    SailRV64.zbb_extop rs1_val extop_zbb.ZEXTH  = zexth rs1_val := by
  simp [SailRV64.zbb_extop, zexth, LeanRV64D.Functions.zero_extend, Sail.BitVec.extractLsb, Sail.BitVec.zeroExtend]

theorem zbb_clz_eq (rs1_val : BitVec 64) :
    SailRV64.zbb_clz rs1_val = clz rs1_val := by
  simp [SailRV64.zbb_clz, clz, LeanRV64D.Functions.to_bits, Sail.get_slice_int,
    Sail.BitVec.countLeadingZeros, BitVec.extractLsb'_eq_setWidth]

theorem zbb_clzw_eq (rs1_val : BitVec 64) :
    SailRV64.zbb_clzw rs1_val = clzw rs1_val := by
  simp [SailRV64.zbb_clzw, clzw, LeanRV64D.Functions.to_bits, Sail.get_slice_int,
    Sail.BitVec.countLeadingZeros, BitVec.extractLsb'_eq_setWidth, Sail.BitVec.extractLsb]

theorem zbb_ctz_eq (rs1_val : BitVec 64) :
    SailRV64.zbb_ctz rs1_val = ctz rs1_val := by
  simp [SailRV64.zbb_ctz, ctz, LeanRV64D.Functions.to_bits, Sail.get_slice_int, BitVec.ctz,
    Sail.BitVec.countTrailingZeros, Sail.BitVec.countLeadingZeros, BitVec.extractLsb'_eq_setWidth]

theorem zbb_ctzw_eq (rs1_val : BitVec 64) :
    SailRV64.zbb_ctzw rs1_val = ctzw rs1_val := by
  simp [SailRV64.zbb_ctzw, ctzw, LeanRV64D.Functions.to_bits, Sail.get_slice_int, BitVec.ctz,
    Sail.BitVec.countTrailingZeros, Sail.BitVec.countLeadingZeros, BitVec.extractLsb'_eq_setWidth,
    Sail.BitVec.extractLsb]

theorem zbb_roriw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64.zbb_roriw shamt rs1_val = roriw shamt rs1_val := by
  simp only [SailRV64.zbb_roriw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Nat.sub_zero, Nat.reduceAdd, LeanRV64D.Functions.rotate_bits_right, LeanRV64D.Functions.rotater,
    Sail.shiftr, Sail.BitVec.extractLsb, Sail.BitVec.toNatInt, Int.ofNat_eq_coe, Int.toNat_natCast,
    Int.cast_ofNat_Int, Int.toNat_sub', Int.reduceToNat, BitVec.signExtend_or, roriw,
    BitVec.ushiftRight_eq', BitVec.ofNat_eq_ofNat, BitVec.reduceOfNat, BitVec.zero_sub,
    BitVec.shiftLeft_eq', BitVec.toNat_neg, Nat.reducePow, Sail.shiftl]
  by_cases hzero : shamt.toNat = 0
  · simp [hzero]
  · congr
    rw [Nat.mod_eq_of_lt (by omega)]

theorem zbb_rori_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64.zbb_rori shamt rs1_val = rori shamt rs1_val := by
  simp only [SailRV64.zbb_rori, LeanRV64D.Functions.rotate_bits_right, LeanRV64D.Functions.rotater,
    Sail.shiftr, Sail.BitVec.toNatInt, LeanRV64D.Functions.log2_xlen, Int.cast_ofNat_Int,
    Int.reduceSub, Int.reduceToNat, Nat.sub_zero, Nat.reduceAdd, Sail.BitVec.extractLsb,
    BitVec.extractLsb_toNat, BitVec.toNat_setWidth, Nat.reducePow, Nat.shiftRight_zero,
    Nat.dvd_refl, Nat.mod_mod_of_dvd, Int.ofNat_eq_coe, Int.natCast_emod, Sail.shiftl,
    rori, BitVec.ushiftRight_eq', BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_eq',
    BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod]
  by_cases hzero : shamt.toNat = 0
  · simp [hzero]
  · have : ((64 : Int) - (((shamt.toNat : Int) % 64) : Int).toNat).toNat = ((64 - shamt.toNat % 64) % 64) := by
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast, Int.toNat_sub',
        Nat.mod_eq_of_lt (a := shamt.toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
      simp
    rw [this]
    congr

/-! ## Zbc: Carry-less multiplication -/

/-! ## Zbs: Single-bit instructions -/

theorem zbs_bclr_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbs_rtype rs1_val rs2_val brop_zbs.BCLR = bclr rs1_val rs2_val := by
  simp [SailRV64.zbs_rtype, Sail.BitVec.extractLsb, bclr, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend]

theorem zbs_bext_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbs_rtype rs1_val rs2_val brop_zbs.BEXT = bext rs1_val rs2_val := by
  simp only [SailRV64.zbs_rtype, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend,
    LeanRV64D.Functions.bool_to_bits, LeanRV64D.Functions.bool_bits_forwards, Sail.shift_bits_left,
    Nat.sub_zero, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.truncate_eq_setWidth,
    BitVec.reduceSetWidth, Sail.BitVec.extractLsb, BitVec.shiftLeft_eq', BitVec.extractLsb_toNat,
    Nat.shiftRight_zero, Nat.reducePow, LeanRV64D.Functions.zeros, BitVec.zero_eq, bext, bne_iff_ne,
    ne_eq, ite_not]
  split
  <;> case _ b heq =>
      simp at heq
      simp [heq]

theorem zbs_binv_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbs_rtype rs1_val rs2_val brop_zbs.BINV = binv rs1_val rs2_val := by
  simp [SailRV64.zbs_rtype, Sail.shift_bits_left, Nat.sub_zero, Nat.reduceAdd, LeanRV64D.Functions.zero_extend,
    Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, binv]

theorem zbs_bset_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbs_rtype rs1_val rs2_val brop_zbs.BSET = bset rs1_val rs2_val := by
  simp [SailRV64.zbs_rtype, Sail.shift_bits_left, Nat.sub_zero, Nat.reduceAdd, LeanRV64D.Functions.zero_extend,
    Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, bset]

theorem zbs_iop_bclri_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64.zbs_iop shamt rs1_val biop_zbs.BCLRI = bclri shamt rs1_val := by
  simp [SailRV64.zbs_iop, bclri, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend]

theorem zbs_iop_bexti_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64.zbs_iop shamt rs1_val biop_zbs.BEXTI = bexti shamt rs1_val := by
  simp only [SailRV64.zbs_iop, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend,
    LeanRV64D.Functions.bool_to_bits, LeanRV64D.Functions.bool_bits_forwards, Sail.shift_bits_left,
    BitVec.ofNat_eq_ofNat, BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth, BitVec.shiftLeft_eq',
    LeanRV64D.Functions.zeros, BitVec.zero_eq, bexti, bne_iff_ne, ne_eq, ite_not]
  split
  <;> case _ b heq =>
      simp at heq
      simp [heq]

theorem zbs_iop_binvi_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64.zbs_iop shamt rs1_val biop_zbs.BINVI = binvi shamt rs1_val := by
  simp [SailRV64.zbs_iop, binvi, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend]

theorem zbs_iop_bseti_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64.zbs_iop shamt rs1_val biop_zbs.BSETI = bseti shamt rs1_val := by
  simp [SailRV64.zbs_iop, bseti, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend]

/-! ## Zbkb: Bit-manipulation for Cryptography-/

theorem zbkb_rtype_pack_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbkb_rtype rs1_val rs2_val brop_zbkb.PACK = pack rs1_val rs2_val := by
  simp [SailRV64.zbkb_rtype, pack, Sail.BitVec.extractLsb, LeanRV64D.Functions.xlen_bytes]

theorem zbkb_rtype_packh_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbkb_rtype rs1_val rs2_val brop_zbkb.PACKH = packh rs1_val rs2_val := by
  simp [SailRV64.zbkb_rtype, packh, Sail.BitVec.extractLsb, LeanRV64D.Functions.zero_extend,
    Sail.BitVec.zeroExtend]

theorem zbkb_rtype_packw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.zbkb_packw rs1_val rs2_val  = packw rs1_val rs2_val := by
  simp [SailRV64.zbkb_packw, packw, Sail.BitVec.extractLsb, LeanRV64D.Functions.sign_extend,
    Sail.BitVec.signExtend]

/-! ## Zbkc: Carry-less multiplication for Cryptography -/

/-! ## Zbkx: Carry-less multiplication for Cryptography -/
