import RISCV.SailPure
import RISCV.Skeleton

/-!
  Proofs of the equivalence between monadic and monad-free Sail specifications.
-/

open LeanRV64D.Functions

theorem add_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ADDIW  imm rs1 rd = skeleton_unary rs1 rd (SailRV64I.addiw imm) := by
  simp [execute_ADDIW, skeleton_unary, SailRV64I.addiw]

theorem utype_eq_lui (imm : BitVec 20) (rd : regidx):
    execute_UTYPE imm rd (uop.LUI) = skeleton_utype_lui imm rd
    (fun imm' pc => SailRV64I.utype imm' pc uop.LUI) := by
  simp only [execute_UTYPE, sign_extend, Sail.BitVec.signExtend, Nat.reduceAdd,
    BitVec.ofNat_eq_ofNat, bind_pure_comp, pure_bind, skeleton_utype_lui, imp_self, implies_true,
    map_inj_right_of_nonempty]
  rfl

theorem utype_eq_auipc (imm : (BitVec 20)) (rd : regidx):
    execute_UTYPE imm rd (uop.AUIPC) = skeleton_utype_auipc imm rd
    (fun imm' pc => SailRV64I.utype imm' pc uop.AUIPC) := by
  simp [execute_UTYPE, skeleton_utype_auipc, SailRV64I.utype]

theorem utype_eq (imm : (BitVec 20)) (rd : regidx) (op : uop) (h_pc : s.regs.get? Register.PC = some valt):
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
