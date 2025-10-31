import RISCV.SailPure
import RISCV.Skeleton

/-!
  Proofs of the equivalence between monadic and monad-free Sail specifications.
  Ordered as in https://msyksphinz-self.github.io/riscv-isadoc.
-/

open LeanRV64D.Functions

/-! # RV32I, RV64I Instructions -/

theorem utype_lui_eq (imm : BitVec 20) (rd : regidx) :
    execute_UTYPE imm rd uop.LUI = skeleton_utype_lui imm rd
    (fun imm' pc => SailRV64I.utype imm' pc uop.LUI) := by
  simp only [execute_UTYPE, sign_extend, Sail.BitVec.signExtend, Nat.reduceAdd,
    BitVec.ofNat_eq_ofNat, bind_pure_comp, pure_bind, skeleton_utype_lui, imp_self, implies_true,
    map_inj_right_of_nonempty]
  rfl

theorem utype_auipc_eq (imm : BitVec 20) (rd : regidx) :
    execute_UTYPE imm rd uop.AUIPC = skeleton_utype_auipc imm rd
    (fun imm' pc => SailRV64I.utype imm' pc uop.AUIPC) := by
  simp [execute_UTYPE, skeleton_utype_auipc, SailRV64I.utype]

theorem utype_eq (imm : BitVec 20) (rd : regidx) (op : uop) (h_pc : s.regs.get? Register.PC = some valt) :
    execute_UTYPE imm rd op s = skeleton_utype imm rd op SailRV64I.utype s := by
  simp [execute_UTYPE, skeleton_utype, SailRV64I.utype]
  cases op
  · simp only [pure_bind]
    simp only [EStateM.instMonad, EStateM.map, Monad.toBind, get_arch_pc, PreSail.readReg, get,
      getThe, MonadStateOf.get, EStateM.bind, EStateM.get]
    rcases hs : s.regs.get? Register.PC
    · simp [hs] at h_pc
    · simp only
      rfl
  · simp

theorem shiftiop_slli_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SLLI
    = skeleton_unary rs1 rd (fun val => SailRV64I.shiftiop shamt sop.SLLI val) := by
  simp [execute_SHIFTIOP, Sail.shift_bits_left, LeanRV64D.Functions.log2_xlen,
    Sail.BitVec.extractLsb, skeleton_unary, SailRV64I.shiftiop]

theorem shiftiop_srli_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRLI
    = skeleton_unary rs1 rd (fun val => SailRV64I.shiftiop shamt sop.SRLI val) := by
  simp [execute_SHIFTIOP, Sail.shift_bits_right, LeanRV64D.Functions.log2_xlen,
    Sail.BitVec.extractLsb, skeleton_unary, SailRV64I.shiftiop]

theorem shiftiop_srai_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRAI
    = skeleton_unary rs1 rd (fun val => SailRV64I.shiftiop shamt sop.SRAI val) := by
  simp [execute_SHIFTIOP, shift_bits_right_arith, LeanRV64D.Functions.log2_xlen,
    Sail.BitVec.extractLsb, skeleton_unary, SailRV64I.shiftiop]

theorem rtype_add_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.ADD
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.ADD val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

theorem rtype_sub_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SUB
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.SUB val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

theorem rtype_sll_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLL
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.SLL val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

theorem rtype_slt_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLT
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.SLT val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

theorem rtype_sltu_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLTU
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.SLTU val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

theorem rtype_xor_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.XOR
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.XOR val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

theorem rtype_srl_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRL
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.SRL val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

theorem rtype_sra_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRA
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.SRA val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

theorem rtype_or_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.OR
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.OR val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

theorem rtype_and_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.AND
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtype rop.AND val2 val1) := by
  simp [execute_RTYPE, skeleton_binary, SailRV64I.rtype]

/-! # RV64I Instructions -/

theorem addiw_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ADDIW  imm rs1 rd = skeleton_unary rs1 rd (SailRV64I.addiw imm) := by
  simp [execute_ADDIW, skeleton_unary, SailRV64I.addiw]

theorem shiftiwop_slliw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW
    = skeleton_unary rs1 rd (fun val => SailRV64I.shiftiwop shamt sopw.SLLIW val) := by
  simp only [execute_SHIFTIWOP, Nat.sub_zero, Nat.reduceAdd, bind_pure_comp, pure_bind,
    skeleton_unary]
  rfl

theorem shiftiwop_srliw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW
    = skeleton_unary rs1 rd (fun val => SailRV64I.shiftiwop shamt sopw.SRLIW val) := by
  simp only [execute_SHIFTIWOP, Nat.sub_zero, Nat.reduceAdd, bind_pure_comp, pure_bind,
    skeleton_unary]
  rfl

theorem shiftiwop_sraiw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW
    = skeleton_unary rs1 rd (fun val => SailRV64I.shiftiwop shamt sopw.SRAIW val) := by
  simp only [execute_SHIFTIWOP, Nat.sub_zero, Nat.reduceAdd, bind_pure_comp, pure_bind,
    skeleton_unary]
  rfl

theorem rtypew_add_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.ADDW val2 val1) := by
  simp [execute_RTYPEW, skeleton_binary]
  rfl

theorem rtypew_sub_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SUBW
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.SUBW val2 val1) := by
  simp [execute_RTYPEW, skeleton_binary]
  rfl

theorem rtypew_sllw_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.SLLW val2 val1) := by
  simp [execute_RTYPEW, skeleton_binary]
  rfl

theorem rtypew_srlw_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRLW
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.SRLW val2 val1) := by
  simp [execute_RTYPEW, skeleton_binary]
  rfl

theorem rtypew_sraw_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRAW
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.SRAW val2 val1) := by
  simp [execute_RTYPEW, skeleton_binary]
  rfl

/-! # RV32M, RV64M Instructions -/

/-! # RV64M Instructions -/
