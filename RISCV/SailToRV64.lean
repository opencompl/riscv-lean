import RISCV.SailPure
import RISCV.Skeleton

/-!
  Proofs of the equivalence between monadic and monad-free Sail specifications.
  Ordered as in https://docs.riscv.org/reference/isa/unpriv/rv64.html
-/

open LeanRV64D.Functions
open LeanRV64D.Defs

/-! # RV64I Base Integer Instruction Set -/

theorem utype_lui_eq (imm : BitVec 20) (rd : regidx) :
    execute_UTYPE imm rd uop.LUI = skeleton_utype_lui imm rd
    (fun imm' pc => SailRV64.utype imm' pc uop.LUI) := by
  simp only [execute_UTYPE, sign_extend, Sail.BitVec.signExtend, Nat.reduceAdd,
    bind_pure_comp, pure_bind, skeleton_utype_lui, imp_self, implies_true,
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
  · simp only [get_arch_pc, LeanRV64D.readReg,
      Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get]
    rcases hs : s.regs.get? Register.PC
    · simp [hs] at h_pc
    · simp only [EStateM.get, bind, EStateM.bind, hs]
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
  have hf : (fun a : BitVec 64 => (fun _ => RETIRE_SUCCESS) <$> wX_bits rd (a <<< BitVec.setWidth 6 shamt))
          = (fun a : BitVec 64 => (fun _ => RETIRE_SUCCESS) <$> wX_bits rd (a <<< (shamt.toNat % 64))) := by
    funext a; rw [BitVec.shiftLeft_eq', BitVec.toNat_setWidth]
  have he : BitVec.extractLsb 5 0 shamt = BitVec.setWidth 6 shamt := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb_toNat, Nat.shiftRight_zero, BitVec.toNat_setWidth]
  simp [execute_SHIFTIOP, Sail.shift_bits_left, LeanRV64D.Functions.log2_xlen,
    Sail.BitVec.extractLsb, skeleton_unary, SailRV64.shiftiop, he]
  exact congrArg (rX_bits rs1 >>= ·) hf

theorem shiftiop_srli_eq (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRLI
    = skeleton_unary rs1 rd (fun val => SailRV64.shiftiop shamt sop.SRLI val) := by
  have hf : (fun a : BitVec 64 => (fun _ => RETIRE_SUCCESS) <$> wX_bits rd (a >>> BitVec.setWidth 6 shamt))
          = (fun a : BitVec 64 => (fun _ => RETIRE_SUCCESS) <$> wX_bits rd (a >>> (shamt.toNat % 64))) := by
    funext a; rw [BitVec.ushiftRight_eq', BitVec.toNat_setWidth]
  have he : BitVec.extractLsb 5 0 shamt = BitVec.setWidth 6 shamt := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb_toNat, Nat.shiftRight_zero, BitVec.toNat_setWidth]
  simp [execute_SHIFTIOP, Sail.shift_bits_right, LeanRV64D.Functions.log2_xlen,
    Sail.BitVec.extractLsb, skeleton_unary, SailRV64.shiftiop, he]
  exact congrArg (rX_bits rs1 >>= ·) hf

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

theorem zba_slliuw_eq (rs1 : regidx) (rd : regidx) (shamt: BitVec 6) :
    execute_SLLIUW shamt rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zba_slliuw shamt val1) := by rfl

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

/-- A Sail `IntRange` loop whose body is always `pure` (under an invariant `P`) equals
  the corresponding pure loop. -/
theorem IntRange.forIn'_loop_eq_pure {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (range : IntRange) (P : Int → β → Prop)
    (f : (i : Int) → i ∈ range → β → m (ForInStep β)) (g : (i : Int) → i ∈ range → β → β)
    (hf : ∀ i h b, P i b → f i h b = pure (.yield (g i h b)))
    (hP : ∀ i h b, P i b → P (i + range.step) (g i h b))
    (b : β) (i : Int) (hs : (i - range.start) % range.step = 0) (hb : P i b) :
    IntRange.forIn'.loop range f b i hs
      = pure (IntRange.forIn'.loop (m := Id) range (fun i h b => pure (.yield (g i h b))) b i hs).run := by
  induction b, i, hs using IntRange.forIn'.loop.induct range with
  | case1 b i hs hmem ih =>
    rw [IntRange.forIn'.loop, IntRange.forIn'.loop]
    simp only [hmem, ↓reduceDIte, hf i hmem b hb, pure_bind]
    exact ih _ (hP i hmem b hb)
  | case2 b i hs hmem =>
    rw [IntRange.forIn'.loop, IntRange.forIn'.loop]
    simp [hmem]

/-- A Sail `IntRange` loop whose body is `pure` equals the corresponding pure loop. -/
theorem IntRange.forIn'_loop_pure_body {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (range : IntRange) (g : (i : Int) → i ∈ range → β → β)
    (b : β) (i : Int) (hs : (i - range.start) % range.step = 0) :
    IntRange.forIn'.loop (m := m) range (fun i h b => pure (.yield (g i h b))) b i hs
      = pure (IntRange.forIn'.loop (m := Id) range (fun i h b => pure (.yield (g i h b))) b i hs).run :=
  IntRange.forIn'_loop_eq_pure range (fun _ _ => True) _ g (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => trivial) b i hs trivial

theorem zbb_cpop_eq (rs1 : regidx) (rd : regidx) :
    execute_CPOP rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_cpop val1) := by
  unfold execute_CPOP SailRV64.zbb_cpop count_ones SailRV64.count_ones_pure skeleton_unary
  simp only [Int.cast_ofNat_Int, Int.reduceSub, beq_iff_eq, bind_pure_comp, map_pure,
    Functor.map_map, Int.toNat_natCast_add_one, Int.toNat_natCast, bind_pure]
  congr
  funext x
  simp only [forIn, forIn', IntRange.forIn']
  rw [IntRange.forIn'_loop_eq_pure (m := SailM) _ (fun i (b : Nat) => 0 ≤ i ∧ (b : Int) ≤ i)
    (g := fun i _ r => if Sail.BitVec.access x i.toNat = 1#1 then r + 1 else r)]
  · simp
  · intro i h b hb
    simp only [IntRange.instMemIntRange] at h
    split
    · have : (b : Int) + 1 ≤ 64 := by simp at h; omega
      simp [PreSail.assert, this]
    · rfl
  · intros
    simp
    split <;> omega
  · simp

theorem zbb_cpopw_eq (rs1 : regidx) (rd : regidx) :
    execute_CPOPW rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_cpopw val1) := by
  unfold execute_CPOPW SailRV64.zbb_cpopw count_ones SailRV64.count_ones_pure skeleton_unary
  simp only [beq_iff_eq, bind_pure_comp, map_pure, Functor.map_map, Int.toNat_natCast_add_one,
    Int.toNat_natCast, bind_pure]
  congr
  funext x
  simp only [forIn, forIn', IntRange.forIn']
  rw [IntRange.forIn'_loop_eq_pure (m := SailM) _ (fun i (b : Nat) => 0 ≤ i ∧ (b : Int) ≤ i)
    (g := fun i _ r =>
      if Sail.BitVec.access (Sail.BitVec.extractLsb x 31 0) i.toNat = 1#1 then r + 1 else r)]
  · simp
  · intro i h b hb
    simp only [IntRange.instMemIntRange] at h
    split
    · have : (b : Int) + 1 ≤ 32 := by simp at h; omega
      simp [PreSail.assert, this]
    · rfl
  · intro i h b hb
    simp
    split <;> omega
  · simp

theorem zbb_orcb_eq (rs1 : regidx) (rd : regidx) :
    execute_ORCB rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_orcb val1) := by
  unfold execute_ORCB SailRV64.zbb_orcb skeleton_unary
  simp only [forIn, forIn', IntRange.forIn', bind_pure, pure_bind]
  congr 1
  funext x
  rw [IntRange.forIn'_loop_pure_body, pure_bind]

theorem zbb_rev8_eq (rs1 : regidx) (rd : regidx) :
    execute_REV8 rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zbb_rev8 val1) := by rfl

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

/-! # "Zicond" Extension for Integer Conditional Operations -/

theorem readReg_ok_state {r : Register}
    {s s' : PreSail.SequentialState RegisterType Sail.trivialChoiceSource} {a}
    (h : (PreSail.readReg r : SailM _) s = .ok a s') : s' = s := by
  simp only [PreSail.readReg, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get] at h
  revert h
  cases s.regs.get? r <;>
    simp [pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw] <;> simp_all

theorem readReg_error_state {r : Register}
    {s s' : PreSail.SequentialState RegisterType Sail.trivialChoiceSource} {e}
    (h : (PreSail.readReg r : SailM _) s = .error e s') : s' = s := by
  simp only [PreSail.readReg, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get] at h
  revert h
  cases s.regs.get? r <;>
    simp [pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw] <;> simp_all

/-- The value of register `x` in state `s`, or `0` if reading it fails. -/
def rX_pure (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) (x : regidx) :
    BitVec 64 :=
  match (rX_bits x).run s with
  | .ok v _ => v
  | .error _ _ => 0

/-- Reading a register never changes the state. -/
theorem rX_bits_run (x : regidx) (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    (rX_bits x).run s = .ok (rX_pure s x) s ∨ ∃ e, (rX_bits x).run s = .error e s := by
  unfold rX_pure
  rcases x with ⟨i⟩
  simp only [rX_bits, rX, EStateM.run]
  split <;> simp [bind, EStateM.bind, pure, EStateM.pure, Sail.readReg] <;> split <;> simp <;>
    first | exact readReg_ok_state ‹_› | exact readReg_error_state ‹_›

theorem zicond_rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx)
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h : (rX_bits rs1).run s = .ok (rX_pure s rs1) s) :
    (execute_ZICOND_RTYPE rs2 rs1 rd op).run s
    = (skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zicond_rtype val2 val1 op)).run s := by
  simp only [EStateM.run] at h ⊢
  unfold execute_ZICOND_RTYPE SailRV64.zicond_rtype skeleton_binary
  rcases rX_bits_run rs2 s with h2 | ⟨e, h2⟩ <;> simp only [EStateM.run] at h2 <;>
  cases op <;> simp [bind, EStateM.bind, pure, EStateM.pure, h, h2]
  all_goals by_cases hc : rX_pure s rs2 = zeros <;> simp [hc, h, EStateM.pure]

/-! # Pseudo-instructions -/

theorem rX_bits_zreg : rX_bits zreg = pure (zeros (n := 64)) := by rfl

theorem mv_eq (rs1 : regidx) (rd : regidx) :
    execute_ITYPE 0#12 rs1 rd iop.ADDI
    = skeleton_unary rs1 rd (fun val1 => SailRV64.mv val1) := by
  simp [execute_ITYPE, skeleton_unary, SailRV64.mv, SailRV64.itype]

theorem neg_eq (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs1 zreg rd rop.SUB
    = skeleton_unary rs1 rd (fun val1 => SailRV64.neg val1) := by
  simp [execute_RTYPE, skeleton_unary, SailRV64.neg, SailRV64.rtype, rX_bits_zreg]

theorem negw_eq (rs1 : regidx) (rd : regidx) :
    execute_RTYPEW rs1 zreg rd ropw.SUBW
    = skeleton_unary rs1 rd (fun val1 => SailRV64.negw val1) := by rfl

theorem not_eq (rs1 : regidx) (rd : regidx) :
    execute_ITYPE 0xFFF#12 rs1 rd iop.XORI
    = skeleton_unary rs1 rd (fun val1 => SailRV64.not val1) := by
  simp [execute_ITYPE, skeleton_unary, SailRV64.not, SailRV64.itype]

theorem seqz_eq (rs1 : regidx) (rd : regidx) :
    execute_ITYPE 1#12 rs1 rd iop.SLTIU
    = skeleton_unary rs1 rd (fun val1 => SailRV64.seqz val1) := by
  simp [execute_ITYPE, skeleton_unary, SailRV64.seqz, SailRV64.itype]

theorem snez_eq (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs1 zreg rd rop.SLTU
    = skeleton_unary rs1 rd (fun val1 => SailRV64.snez val1) := by
  simp [execute_RTYPE, skeleton_unary, SailRV64.snez, SailRV64.rtype, rX_bits_zreg]

theorem sltz_eq (rs1 : regidx) (rd : regidx) :
    execute_RTYPE zreg rs1 rd rop.SLT
    = skeleton_unary rs1 rd (fun val1 => SailRV64.sltz val1) := by
  simp [execute_RTYPE, skeleton_unary, SailRV64.sltz, SailRV64.rtype, rX_bits_zreg]

theorem sgtz_eq (rs1 : regidx) (rd : regidx) :
    execute_RTYPE rs1 zreg rd rop.SLT
    = skeleton_unary rs1 rd (fun val1 => SailRV64.sgtz val1) := by
  simp [execute_RTYPE, skeleton_unary, SailRV64.sgtz, SailRV64.rtype, rX_bits_zreg]

theorem sextw_eq (rs1 : regidx) (rd : regidx) :
    execute_ADDIW 0#12 rs1 rd
    = skeleton_unary rs1 rd (fun val1 => SailRV64.sextw val1) := by rfl

theorem zextb_eq (rs1 : regidx) (rd : regidx) :
    execute_ITYPE 0xFF#12 rs1 rd iop.ANDI
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zextb val1) := by
  simp [execute_ITYPE, skeleton_unary, SailRV64.zextb, SailRV64.itype]

theorem zextw_eq (rs1 : regidx) (rd : regidx) :
    execute_ZBA_RTYPEUW zreg rs1 rd 0#2
    = skeleton_unary rs1 rd (fun val1 => SailRV64.zextw val1) := by rfl
