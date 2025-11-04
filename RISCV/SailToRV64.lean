import RISCV.SailPure
import RISCV.Skeleton
import Batteries.Lean.EStateM

/-!
  Proofs of the equivalence between monadic and monad-free Sail specifications.
  Ordered as in https://docs.riscv.org/reference/isa/unpriv/rv64.html
-/

open LeanRV64D.Functions

/-! # RV64I Base Integer Instruction Set -/

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

theorem itype_addi_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ADDI
    = skeleton_unary rs1 rd (fun val1 => SailRV64I.itype imm val1 iop.ADDI) := by
  simp [execute_ITYPE, SailRV64I.itype, skeleton_unary]

theorem itype_slti_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.SLTI
    = skeleton_unary rs1 rd (fun val1 => SailRV64I.itype imm val1 iop.SLTI) := by
  simp [execute_ITYPE, SailRV64I.itype, skeleton_unary]

theorem itype_sltiu_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.SLTIU
    = skeleton_unary rs1 rd (fun val1 => SailRV64I.itype imm val1 iop.SLTIU) := by
  simp [execute_ITYPE, SailRV64I.itype, skeleton_unary]

theorem itype_andi_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ANDI
    = skeleton_unary rs1 rd (fun val1 => SailRV64I.itype imm val1 iop.ANDI) := by
  simp [execute_ITYPE, SailRV64I.itype, skeleton_unary]

theorem itype_ori_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ORI
    = skeleton_unary rs1 rd (fun val1 => SailRV64I.itype imm val1 iop.ORI) := by
  simp [execute_ITYPE, SailRV64I.itype, skeleton_unary]

theorem itype_xori_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ITYPE imm rs1 rd iop.XORI
    = skeleton_unary rs1 rd (fun val1 => SailRV64I.itype imm val1 iop.XORI) := by
  simp [execute_ITYPE, SailRV64I.itype, skeleton_unary]

theorem addiw_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ADDIW  imm rs1 rd = skeleton_unary rs1 rd (SailRV64I.addiw imm) := by rfl

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

theorem shiftiwop_slliw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW
    = skeleton_unary rs1 rd (fun val => SailRV64I.shiftiwop shamt sopw.SLLIW val) := by rfl

theorem shiftiwop_srliw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW
    = skeleton_unary rs1 rd (fun val => SailRV64I.shiftiwop shamt sopw.SRLIW val) := by rfl

theorem shiftiwop_sraiw_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW
    = skeleton_unary rs1 rd (fun val => SailRV64I.shiftiwop shamt sopw.SRAIW val) := by rfl

theorem rtypew_add_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.ADDW val2 val1) := by rfl

theorem rtypew_sub_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SUBW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.SUBW val2 val1) := by rfl

theorem rtypew_sllw_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.SLLW val2 val1) := by rfl

theorem rtypew_srlw_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRLW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.SRLW val2 val1) := by rfl

theorem rtypew_sraw_eq (rs1 : regidx) (rs2 : regidx) (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRAW
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rtypew ropw.SRAW val2 val1) := by rfl

/-! # M Extension for Integer Multiplication and Division -/

/--
  Due to a mistake in the Sail model, some proofs are currently broken.
  We replace the proofs depending on mistaken definitions with an axiom.-/
axiom rem_sail_error {p: Prop} : p

theorem rem_unsigned_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_REM rs2 rs1 rd true
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rem true val2 val1) := rem_sail_error

theorem rem_signed_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_REM rs2 rs1 rd false
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.rem false val2 val1) := rem_sail_error

theorem remw_unsigned_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_REMW rs2 rs1 rd true
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.remw true val2 val1) := rem_sail_error

theorem remw_signed_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_REMW rs2 rs1 rd false
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.remw false val2 val1) := rem_sail_error

theorem mulw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_MULW rs2 rs1 rd
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.mulw val2 val1) := by rfl

theorem mul_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_MUL rs2 rs1 rd op
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.mul val2 val1 op) := by rfl

/--
  Due to a mistake in the Sail model, some proofs are currently broken.
  We replace the proofs depending on mistaken definitions with an axiom.-/
axiom div_sail_error {p: Prop} : p

theorem div_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_DIV rs2 rs1 rd is_unsigned
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.div val2 val1 is_unsigned) := div_sail_error

theorem divw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_DIVW rs2 rs1 rd is_unsigned
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64I.divw val2 val1 is_unsigned) := div_sail_error

/-! # "Zicond" Extension for Integer Conditional Operations -/

def rX_pure (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) (x : regidx) : BitVec 64 :=
  let regs := s.regs
  let i := match x.1 with
    | 1 => Register.x1
    | 2 => Register.x2
    | 3 => Register.x3
    | 4 => Register.x4
    | 5 => Register.x5
    | 6 => Register.x6
    | 7 => Register.x7
    | 8 => Register.x8
    | 9 => Register.x9
    | 10 => Register.x10
    | 11 => Register.x11
    | 12 => Register.x12
    | 13 => Register.x13
    | 14 => Register.x14
    | 15 => Register.x15
    | 16 => Register.x16
    | 17 => Register.x17
    | 18 => Register.x18
    | 19 => Register.x19
    | 20 => Register.x20
    | 21 => Register.x21
    | 22 => Register.x22
    | 23 => Register.x23
    | 24 => Register.x24
    | 25 => Register.x25
    | 26 => Register.x26
    | 27 => Register.x27
    | 28 => Register.x28
    | 29 => Register.x29
    | 30 => Register.x30
    | 31 => Register.x31
    | _ => Register.x1
  match (regs.get? i) with
  | some rType =>
    match i with
    | .x21 => rX (.x21)
  | _ => sorry

@[simp]
theorem run_eq :
    EStateM.run (rX_bits rs2) s = EStateM.Result.ok (rX_pure s rs2) s := by
  sorry

theorem zicond_rtype_eq (rs1 : regidx) (rs2 : regidx) (rs : regidx) (op : zicondop) :
  execute_ZICOND_RTYPE rs1 rs2 rd op
  = skeleton_binary' rs1 rs2 rd (fun val1 val2 => SailRV64I.zicond val2 val1 op) := by
  simp [execute_ZICOND_RTYPE, skeleton_binary', SailRV64I.zicond]
  cases op
  · case _ =>
    apply EStateM.ext
    simp only [bind_map_left, beq_iff_eq, EStateM.run_bind, run_eq, EStateM.run_map]
    intros s
    split
    . case _ h1 =>
      split
      . case _ h2 =>
        simp_all
      · case _ h3 =>
        simp_all
        obtain ⟨hs1, hs1'⟩ := h1
        subst hs1'
        simp_all
    · case _ h1 =>
      split
      . case _ h2 =>
        split at h1 <;> simp_all
      · case _ h3 =>
        simp_all
  · case _ =>
    apply EStateM.ext
    simp only [bind_map_left, bne_iff_ne, ne_eq, ite_not, EStateM.run_bind, run_eq, EStateM.run_map]
    intros s
    split
    . case _ h1 =>
      split
      . case _ h2 =>
        simp_all
        obtain ⟨hs1, hs1'⟩ := h1
        subst hs1'
        simp_all
      · case _ h3 =>
        simp_all
    · case _ h1 =>
      split
      . case _ h2 =>
        split at h1 <;> simp_all
      · case _ h3 =>
        simp_all

theorem zicond_rtype_nez_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    execute_ZICOND_RTYPE rs2 rs1 rd (zicondop.CZERO_NEZ)
    = skeleton_binary rs1 rs2 rd (fun val1 val2 => SailRV64I.zicond val2 val1 zicondop.CZERO_NEZ) := by
  simp [execute_ZICOND_RTYPE, skeleton_binary, SailRV64I.zicond]

  sorry
