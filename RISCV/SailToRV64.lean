import RISCV.SailPure
import RISCV.Skeleton

/-!
  Proofs of the equivalence between monadic and monad-free Sail specifications.
  Ordered as in https://docs.riscv.org/reference/isa/unpriv/rv64.html
-/

open LeanRV64D.Functions

/-! # RV64I Base Integer Instruction Set -/

theorem utype_lui_eq (imm : BitVec 20) (rd : regidx) :
    execute_UTYPE imm rd uop.LUI = skeleton_utype_lui imm rd
    (fun imm' pc => SailRV64.utype imm' pc uop.LUI) := by
  simp only [execute_UTYPE, sign_extend, Sail.BitVec.signExtend, Nat.reduceAdd,
    BitVec.ofNat_eq_ofNat, bind_pure_comp, pure_bind, skeleton_utype_lui, imp_self, implies_true,
    map_inj_right_of_nonempty]
  rfl

theorem utype_auipc_eq (imm : BitVec 20) (rd : regidx) :
    execute_UTYPE imm rd uop.AUIPC = skeleton_utype_auipc imm rd
    (fun imm' pc => SailRV64.utype imm' pc uop.AUIPC) := by
  simp [execute_UTYPE, skeleton_utype_auipc, SailRV64.utype]

theorem utype_eq (imm : BitVec 20) (rd : regidx) (op : uop) (h_pc : s.regs.get? Register.PC = some valt) :
    execute_UTYPE imm rd op s = skeleton_utype imm rd op SailRV64.utype s := by
  simp [execute_UTYPE, skeleton_utype, SailRV64.utype]
  cases op
  · simp only [pure_bind]
    simp only [EStateM.instMonad, EStateM.map, Monad.toBind, get_arch_pc, PreSail.readReg, get,
      getThe, MonadStateOf.get, EStateM.bind, EStateM.get]
    rcases hs : s.regs.get? Register.PC
    · simp [hs] at h_pc
    · simp only
      rfl
  · simp

theorem itype_addi_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ADDI
    = skeleton_unary rs1 rd (fun val1 => SailRV64.itype imm val1 iop.ADDI) := by
  simp [execute_ITYPE, SailRV64.itype, skeleton_unary]

theorem itype_slti_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.SLTI
    = skeleton_unary rs1 rd (fun val1 => SailRV64.itype imm val1 iop.SLTI) := by
  simp [execute_ITYPE, SailRV64.itype, skeleton_unary]

theorem itype_sltiu_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.SLTIU
    = skeleton_unary rs1 rd (fun val1 => SailRV64.itype imm val1 iop.SLTIU) := by
  simp [execute_ITYPE, SailRV64.itype, skeleton_unary]

theorem itype_andi_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ANDI
    = skeleton_unary rs1 rd (fun val1 => SailRV64.itype imm val1 iop.ANDI) := by
  simp [execute_ITYPE, SailRV64.itype, skeleton_unary]

theorem itype_ori_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ORI
    = skeleton_unary rs1 rd (fun val1 => SailRV64.itype imm val1 iop.ORI) := by
  simp [execute_ITYPE, SailRV64.itype, skeleton_unary]

theorem itype_xori_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.XORI
    = skeleton_unary rs1 rd (fun val1 => SailRV64.itype imm val1 iop.XORI) := by
  simp [execute_ITYPE, SailRV64.itype, skeleton_unary]

theorem addiw_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ADDIW  imm rs1 rd = skeleton_unary rs1 rd (SailRV64.addiw imm) := by rfl

theorem shiftiop_slli_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SLLI
    = skeleton_unary rs1 rd (fun val => SailRV64.shiftiop shamt sop.SLLI val) := by
  simp [execute_SHIFTIOP, Sail.shift_bits_left, LeanRV64D.Functions.log2_xlen,
    Sail.BitVec.extractLsb, skeleton_unary, SailRV64.shiftiop]

theorem shiftiop_srli_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRLI
    = skeleton_unary rs1 rd (fun val => SailRV64.shiftiop shamt sop.SRLI val) := by
  simp [execute_SHIFTIOP, Sail.shift_bits_right, LeanRV64D.Functions.log2_xlen,
    Sail.BitVec.extractLsb, skeleton_unary, SailRV64.shiftiop]

theorem shiftiop_srai_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRAI
    = skeleton_unary rs1 rd (fun val => SailRV64.shiftiop shamt sop.SRAI val) := by
  simp [execute_SHIFTIOP, shift_bits_right_arith, LeanRV64D.Functions.log2_xlen,
    Sail.BitVec.extractLsb, skeleton_unary, SailRV64.shiftiop]
  congr
  ext a
  congr
  bv_decide

theorem rtype_add_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.ADD
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.ADD val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem rtype_sub_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SUB
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.SUB val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem rtype_sll_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLL
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.SLL val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem rtype_slt_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLT
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.SLT val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem rtype_sltu_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLTU
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.SLTU val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem rtype_xor_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.XOR
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.XOR val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem rtype_srl_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRL
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.SRL val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem rtype_sra_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRA
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.SRA val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem rtype_or_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.OR
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.OR val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem rtype_and_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.AND
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype rop.AND val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64.rtype]

theorem shiftiwop_slliw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW
    = skeleton_unary rs1 rd (fun val => SailRV64.shiftiwop shamt sopw.SLLIW val) := by rfl

theorem shiftiwop_srliw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW
    = skeleton_unary rs1 rd (fun val => SailRV64.shiftiwop shamt sopw.SRLIW val) := by rfl

theorem shiftiwop_sraiw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW
    = skeleton_unary rs1 rd (fun val => SailRV64.shiftiwop shamt sopw.SRAIW val) := by rfl

theorem rtypew_add_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtypew ropw.ADDW val2 val1) := by rfl

theorem rtypew_sub_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SUBW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtypew ropw.SUBW val2 val1) := by rfl

theorem rtypew_sllw_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtypew ropw.SLLW val2 val1) := by rfl

theorem rtypew_srlw_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRLW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtypew ropw.SRLW val2 val1) := by rfl

theorem rtypew_sraw_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRAW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtypew ropw.SRAW val2 val1) := by rfl

/-! # M Extension for Integer Multiplication and Division -/


theorem rem_unsigned_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_REM rs2 rs1 rd true
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rem true val2 val1) := rfl

theorem rem_signed_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_REM rs2 rs1 rd false
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rem false val2 val1) := rfl

theorem remw_unsigned_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_REMW rs2 rs1 rd true
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.remw true val2 val1) := rfl

theorem remw_signed_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_REMW rs2 rs1 rd false
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.remw false val2 val1) := rfl

theorem mulw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_MULW rs2 rs1 rd
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.mulw val2 val1) := by rfl

theorem mul_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_MUL rs2 rs1 rd op
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.mul val2 val1 op) := by rfl


theorem div_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_DIV rs2 rs1 rd is_unsigned
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.div val2 val1 is_unsigned) := rfl

theorem divw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_DIVW rs2 rs1 rd is_unsigned
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.divw val2 val1 is_unsigned) := rfl

/-! # "B" Extension for Bit Manipulation -/

/-! ## Zba: Address generation -/

theorem zba_rtypeuw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (shamt : BitVec 2):
    execute_ZBA_RTYPEUW rs2 rs1 rd shamt
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zba_rtypeuw val2 val1 shamt) := by rfl

theorem zba_rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (shamt : BitVec 2):
    execute_ZBA_RTYPE rs2 rs1 rd shamt
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zba_rtype val2 val1 shamt) := by rfl

/-! ## Zbb: Basic bit-manipulation -/

theorem zbb_rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_ZBB_RTYPE rs2 rs1 rd op
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zbb_rtype val2 val1 op) := by rfl

theorem zbb_rtypew_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_ZBB_RTYPEW rs2 rs1 rd op
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zbb_rtypew val2 val1 op) := by rfl

theorem zbb_extop_eq (rs1 : regidx) (rd : regidx) :
    execute_ZBB_EXTOP rs1 rd op
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_extop val1 op) := by rfl

theorem zbb_clz_eq (rs1 : regidx) (rd : regidx) :
    execute_CLZ rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_clz val1) := by rfl

theorem zbb_clzw_eq (rs1 : regidx) (rd : regidx) :
    execute_CLZW rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_clzw val1) := by rfl

theorem zbb_ctz_eq (rs1 : regidx) (rd : regidx) :
    execute_CTZ rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_ctz val1) := by rfl

theorem zbb_ctzw_eq (rs1 : regidx) (rd : regidx) :
    execute_CTZW rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_ctzw val1) := by rfl

theorem zbb_roriw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_RORIW shamt rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_roriw shamt val1) := by rfl

theorem zbb_rori_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_RORI shamt rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_rori shamt val1) := by rfl

/-! ## Zbc: Carry-less multiplication -/

/-! ## Zbs: Single-bit instructions -/

theorem zbs_rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_ZBS_RTYPE rs2 rs1 rd op
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zbs_rtype val2 val1 op) := by rfl

theorem zbs_iop_eq (shamt : BitVec 6) (rs1 : regidx) (rd : regidx) :
    execute_ZBS_IOP shamt rs1 rd op
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbs_iop shamt val1 op) := by rfl

/-! ## Zbkb: Bit-manipulation for Cryptography-/

theorem zbkb_rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_ZBKB_RTYPE rs2 rs1 rd op
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zbkb_rtype val2 val1 op) := by rfl

theorem zbkb_packw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_ZBKB_PACKW rs2 rs1 rd
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zbkb_packw val2 val1) := by rfl

/-! ## Zbkc: Carry-less multiplication for Cryptography -/

/-! ## Zbkx: Carry-less multiplication for Cryptography -/
