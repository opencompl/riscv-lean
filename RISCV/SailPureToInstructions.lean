import RISCV.SailPure
import RISCV.Instructions
import RISCV.ForLean
import LeanRV64D.Arithmetic

/-!
  Proofs of the equivalence between monad-free Sail specifications and bitvec-only semantics for
  RISCV operations.
  Ordered as in https://docs.riscv.org/reference/isa/unpriv/rv64.html
-/

namespace RV64I

/-! # RV64I Base Integer Instruction Set -/

theorem utype_lui_eq (imm : BitVec 20) (pc : BitVec 64) :
    SailRV64I.utype imm pc (uop.LUI) = RV64I.lui imm pc := by
  simp [SailRV64I.utype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, lui]

theorem utype_auipc_eq (imm : BitVec 20) (pc : BitVec 64) :
    SailRV64I.utype imm pc (uop.AUIPC) = RV64I.auipc imm pc := by
  simp [SailRV64I.utype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, auipc, BitVec.add_comm]

theorem itype_addi_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64I.itype imm rs1_val iop.ADDI = addi imm rs1_val := by
  simp [SailRV64I.itype, addi, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]

theorem itype_slti_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64I.itype imm rs1_val iop.SLTI = slti imm rs1_val := by
  simp [SailRV64I.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, LeanRV64D.Functions.zero_extend, LeanRV64D.Functions.bool_to_bits, Sail.BitVec.zeroExtend, LeanRV64D.Functions.bool_bits_forwards, LeanRV64D.Functions.zopz0zI_s, slti]
  split <;>
  case _ arg h =>
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.slt, h]

theorem itype_sltiu_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64I.itype imm rs1_val iop.SLTIU = sltiu imm rs1_val := by
  simp [SailRV64I.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, LeanRV64D.Functions.zero_extend, LeanRV64D.Functions.bool_to_bits, Sail.BitVec.zeroExtend, LeanRV64D.Functions.bool_bits_forwards, LeanRV64D.Functions.zopz0zI_u, sltiu, Sail.BitVec.toNatInt]
  split <;>
  case _ arg h =>
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.ult, h]

theorem itype_andi_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64I.itype imm rs1_val iop.ANDI = andi imm rs1_val := by
  simp [SailRV64I.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, andi]

theorem itype_ori_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64I.itype imm rs1_val iop.ORI = ori imm rs1_val := by
  simp [SailRV64I.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, ori]

theorem itype_xori_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64I.itype imm rs1_val iop.XORI = xori imm rs1_val := by
  simp [SailRV64I.itype, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, xori]

theorem addiw_eq (imm : BitVec 12) (rs1_val : BitVec 64) :
    SailRV64I.addiw imm rs1_val = RV64I.addiw imm rs1_val := by
  simp only [SailRV64I.addiw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend, Nat.sub_zero,
    Nat.reduceAdd, Sail.BitVec.extractLsb, RV64I.addiw]
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
    BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one,
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
    SailRV64I.rtype rop.SLTU rs2_val rs1_val = RV64I.sltu rs2_val rs1_val := by
  simp [SailRV64I.rtype, RV64I.sltu]
  simp [LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend, LeanRV64D.Functions.bool_to_bits,
    Sail.BitVec.toNatInt, LeanRV64D.Functions.bool_bits_forwards, LeanRV64D.Functions.zopz0zI_u]
  by_cases h : rs1_val.toNat < rs2_val.toNat <;>
  simp [h, BitVec.ult]

theorem rtype_xor_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.XOR rs2_val rs1_val = RV64I.xor rs2_val rs1_val := by rfl

theorem rtype_srl_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.SRL rs2_val rs1_val = RV64I.srl rs2_val rs1_val := by rfl

theorem rtype_sra_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.SRA rs2_val rs1_val = RV64I.sra rs2_val rs1_val := by
  simp only [SailRV64I.rtype, Nat.sub_zero, sra, Nat.reduceAdd, BitVec.sshiftRight_eq',
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow,
    BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one]
  rfl

theorem rtype_or_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.OR rs2_val rs1_val = RV64I.or rs2_val rs1_val := by rfl

theorem rtype_and_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rtype rop.AND rs2_val rs1_val = RV64I.and rs2_val rs1_val := by rfl

theorem shiftiwop_slliw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64I.shiftiwop shamt sopw.SLLIW rs1_val = slliw shamt rs1_val := by
  simp [SailRV64I.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Sail.shift_bits_left, Sail.BitVec.extractLsb, slliw, BitVec.extractLsb'_eq_extractLsb,
    Nat.mod_eq_of_lt (a := shamt.toNat) (b := 64) (by omega)]

theorem shiftiwop_srliw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64I.shiftiwop shamt sopw.SRLIW rs1_val = srliw shamt rs1_val := by
  simp [SailRV64I.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    Sail.shift_bits_right, Sail.BitVec.extractLsb, srliw, BitVec.extractLsb'_eq_extractLsb,
    Nat.mod_eq_of_lt (a := shamt.toNat) (b := 64) (by omega)]

theorem shiftiwop_sraiw_eq (shamt : BitVec 5) (rs1_val : BitVec 64) :
    SailRV64I.shiftiwop shamt sopw.SRAIW rs1_val = sraiw shamt rs1_val := by
  simp only [SailRV64I.shiftiwop, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.shift_bits_right_arith, LeanRV64D.Functions.shift_right_arith,
    Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceSub, sraiw, Nat.sub_zero, Nat.reduceAdd,
    BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend, Nat.add_one_sub_one]
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
    sraw, BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend,
    Nat.add_one_sub_one, Sail.BitVec.toNatInt]
  rfl

/-! # M Extension for Integer Multiplication and Division -/

theorem rem_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.rem false rs1_val rs2_val = rem rs1_val rs2_val := by
  simp only [SailRV64I.rem, rem, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int,
    Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (h := by simp)]
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
    rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_ofInt, Nat.reducePow, BitVec.toInt_umod, h1', reduceIte]
    congr

theorem remw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.remw False rs1_val rs2_val = remw rs1_val rs2_val := by
  simp only [SailRV64I.remw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
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
    SailRV64I.remw True rs1_val rs2_val = remuw rs1_val rs2_val := by
  simp only [SailRV64I.remw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
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
    SailRV64I.mul rs1_val rs2_val {result_part := VectorHalf.Low, signed_rs1 := Signedness.Signed, signed_rs2 := Signedness.Signed} =
      mul rs1_val rs2_val := by
  have h1: rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  have h2 : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp [SailRV64I.mul, LeanRV64D.Functions.mult_to_bits_half, Sail.BitVec.extractLsb,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, mul, BitVec.extractLsb,
    h2, h1, BitVec.ofInt_mul, BitVec.extractLsb'_eq_setWidth, BitVec.setWidth_mul,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_signExtend_eq_self]


theorem mulh_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.mul rs1_val rs2_val {result_part := VectorHalf.High, signed_rs1 := Signedness.Signed, signed_rs2 := Signedness.Signed} =
      mulh rs1_val rs2_val := by
  have h1 : rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  have h2 : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp only [SailRV64I.mul, LeanRV64D.Functions.mult_to_bits_half, Int.cast_ofNat_Int,
    Int.reduceMul, Int.reduceSub, Int.reduceToNat, Nat.reduceSub, Nat.reduceAdd,
    Sail.BitVec.extractLsb, BitVec.extractLsb, LeanRV64D.Functions.to_bits_truncate,
    Sail.get_slice_int, h2, h1, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.extractLsb'_eq_setWidth, mulh]
  rw [BitVec.extractLsb'_setWidth_of_le (by omega), BitVec.setWidth_eq_extractLsb' (by omega)]
  simp


theorem mulhu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.mul rs1_val rs2_val {result_part := VectorHalf.High, signed_rs1 := Signedness.Unsigned, signed_rs2 := Signedness.Unsigned} =
      mulhu rs1_val rs2_val := by
    simp only [SailRV64I.mul, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.cast_ofNat_Int,
      Int.reduceMul, Int.reduceToNat, Int.reduceSub, Nat.reduceSub, Nat.reduceAdd,
      LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, mulhu, BitVec.truncate_eq_setWidth,
      BitVec.extractLsb'_eq_self, LeanRV64D.Functions.mult_to_bits_half]
    rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
    congr

theorem mulhsu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.mul rs1_val rs2_val {result_part := VectorHalf.High, signed_rs1 := Signedness.Signed, signed_rs2 := Signedness.Unsigned} =
      mulhsu rs1_val rs2_val := by
  simp [SailRV64I.mul, LeanRV64D.Functions.mult_to_bits_half, Sail.BitVec.extractLsb,
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
    SailRV64I.mulw rs1_val rs2_val = mulw rs1_val rs2_val := by
  simp only [SailRV64I.mulw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Sail.BitVec.extractLsb, mulw]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (h := by simp), BitVec.extractLsb]
  congr
  apply BitVec.eq_of_toInt_eq
  simp

theorem div_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.div rs1_val rs2_val False = div rs1_val rs2_val := by
  simp only [SailRV64I.div, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
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
    SailRV64I.divw rs1_val rs2_val False = divw rs1_val rs2_val := by
  simp only [SailRV64I.divw, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
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
    SailRV64I.div rs1_val rs2_val True = divu rs1_val rs2_val := by
  simp only [SailRV64I.div, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
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
    SailRV64I.divw rs1_val rs2_val True = divuw rs1_val rs2_val := by
  simp only [SailRV64I.divw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
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

theorem zbs_bclr_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.zbs_rtype rs1_val rs2_val brop_zbs.BCLR = bclr rs1_val rs2_val := by
  simp [SailRV64I.zbs_rtype, Sail.BitVec.extractLsb, bclr, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend]

theorem zbs_bext_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.zbs_rtype rs1_val rs2_val brop_zbs.BEXT = bext rs1_val rs2_val := by
  simp only [SailRV64I.zbs_rtype, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend,
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
    SailRV64I.zbs_rtype rs1_val rs2_val brop_zbs.BINV = binv rs1_val rs2_val := by
  simp [SailRV64I.zbs_rtype, Sail.shift_bits_left, Nat.sub_zero, Nat.reduceAdd, LeanRV64D.Functions.zero_extend,
    Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, binv]

theorem zbs_bset_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.zbs_rtype rs1_val rs2_val brop_zbs.BSET = bset rs1_val rs2_val := by
  simp [SailRV64I.zbs_rtype, Sail.shift_bits_left, Nat.sub_zero, Nat.reduceAdd, LeanRV64D.Functions.zero_extend,
    Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, bset]

theorem zbs_iop_bclri_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.zbs_iop shamt rs1_val biop_zbs.BCLRI = bclri shamt rs1_val := by
  simp [SailRV64I.zbs_iop, bclri, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend]

theorem zbs_iop_bexti_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.zbs_iop shamt rs1_val biop_zbs.BEXTI = bexti shamt rs1_val := by
  simp only [SailRV64I.zbs_iop, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend,
    LeanRV64D.Functions.bool_to_bits, LeanRV64D.Functions.bool_bits_forwards, Sail.shift_bits_left,
    BitVec.ofNat_eq_ofNat, BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth, BitVec.shiftLeft_eq',
    LeanRV64D.Functions.zeros, BitVec.zero_eq, bexti, bne_iff_ne, ne_eq, ite_not]
  split
  <;> case _ b heq =>
      simp at heq
      simp [heq]

theorem zbs_iop_binvi_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.zbs_iop shamt rs1_val biop_zbs.BINVI = binvi shamt rs1_val := by
  simp [SailRV64I.zbs_iop, binvi, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend]

theorem zbs_iop_bseti_eq (shamt : BitVec 6) (rs1_val : BitVec 64) :
    SailRV64I.zbs_iop shamt rs1_val biop_zbs.BSETI = bseti shamt rs1_val := by
  simp [SailRV64I.zbs_iop, bseti, Sail.shift_bits_left, LeanRV64D.Functions.zero_extend, Sail.BitVec.zeroExtend]

theorem zbkb_rtype_pack_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.zbkb_rtype rs1_val rs2_val brop_zbkb.PACK = pack rs1_val rs2_val := by
  simp [SailRV64I.zbkb_rtype, pack, Sail.BitVec.extractLsb, LeanRV64D.Functions.xlen_bytes]

theorem zbkb_rtype_packh_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.zbkb_rtype rs1_val rs2_val brop_zbkb.PACKH = packh rs1_val rs2_val := by
  simp [SailRV64I.zbkb_rtype, packh, Sail.BitVec.extractLsb, LeanRV64D.Functions.zero_extend,
    Sail.BitVec.zeroExtend]

theorem zbkb_rtype_packw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64I.zbkb_packw rs1_val rs2_val  = packw rs1_val rs2_val := by
  simp [SailRV64I.zbkb_packw, packw, Sail.BitVec.extractLsb, LeanRV64D.Functions.sign_extend,
    Sail.BitVec.signExtend]
