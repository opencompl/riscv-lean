import LeanRV64D.Sail.Sail
import LeanRV64D.Sail.BitVec
import LeanRV64D.Specialization
import LeanRV64D.RiscvExtras
import LeanRV64D
import LeanRV64D.InstRetire
import RISCV.SailPure

/-!
  # Correctness of `RISCV64` Dialect Semantics
  This file contains the proofs of correctness of our RISCV `RISCV64` dialect semantics against the Sail model `LeanRV64D`.
-/

open LeanRV64D.Functions

/-!
  ## Skeletons
  We implement skeletons to wrap the execution of functions taking different inputs and
  writing to a destination register into Sail monads.
-/

/-- Given a function `execute_func` with two source registers `rs1`, `rs2` and a destination register `rd`,
  read the values from the source registers and write the result of the function to the destination register.
-/
def skeleton_binary  (rs2 : regidx) (rs1 : regidx) (rd : regidx)
    (execute_func : BitVec 64 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result := execute_func rs1_val rs2_val
  wX_bits rd result
  pure RETIRE_SUCCESS

/-- Given a function `execute_func` with one source register `rs1` and a destination register `rd`,
  read the value from the source register and write the result of the function to the destination register.
-/
def skeleton_unary (rs1 : regidx) (rd : regidx) (execute_func : BitVec 64 → BitVec 64) :
    SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let result := execute_func rs1_val
  wX_bits rd result
  pure RETIRE_SUCCESS

/-- Given an operation `op` with one immediate argument `imm` and a destination register `rd`,
  read the `pc` value and write the result of `op` to the destination register.
-/
def skeleton_UTYPE  (imm : BitVec 20) (rd : regidx) (op : uop)
    (execute_func : BitVec 20 → BitVec 64 → uop → BitVec 64) : SailM ExecutionResult := do
  let pc ← get_arch_pc ()
  let result := execute_func imm pc op
  wX_bits rd result
  pure RETIRE_SUCCESS

/-- Given a function `execute_func` with one immediate argument `imm` and a destination register `rd`,
  read the `pc` value and write the result of `execute_func` to the destination register.
-/
def skeleton_UTYPE_AUIPC  (imm : BitVec 20) (rd : regidx)
    (execute_func : BitVec 20 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let pc ← get_arch_pc ();
  let result := execute_func imm pc
  wX_bits rd result
  pure RETIRE_SUCCESS

/-- Given a function `execute_func` with one immediate argument `imm` and a destination register `rd`,
  write the result of `execute_func` to the destination register.
-/
def skeleton_UTYPE_LUI  (imm : BitVec 20) (rd : regidx)
    (execute_func : BitVec 20 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let result := execute_func imm 0#64
  wX_bits rd result
  pure RETIRE_SUCCESS


theorem add_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    execute_ADDIW (imm) (rs1) (rd) = skeleton_unary rs1 rd (RV64I.addiw imm) := by
  simp [execute_ADDIW, skeleton_unary, RV64I.addiw]
