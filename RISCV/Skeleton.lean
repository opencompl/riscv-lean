import LeanRV64D
open LeanRV64D.Functions

/-!
  # Skeletons
  We implement skeletons to wrap the execution of functions taking different inputs and
  writing to a destination register into Sail monads.
-/

/-- Given a function `execute_func` with two source registers `rs1`, `rs2` and a destination register `rd`,
  read the values in reverse order from the source registers and write the result of the function to the destination register.
-/
def skeleton_binary  (rs2 : regidx) (rs1 : regidx) (rd : regidx)
    (execute_func : BitVec 64 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result := execute_func rs1_val rs2_val
  wX_bits rd result
  pure RETIRE_SUCCESS

/-- Given a function `execute_func` with two source registers `rs1`, `rs2` and a destination register `rd`,
  read the values from the source registers and write the result of the function
  to the destination register.
-/
def skeleton_binary'  (rs2 : regidx) (rs1 : regidx) (rd : regidx)
    (execute_func : BitVec 64 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let rs2_val ← rX_bits rs2
  let rs1_val ← rX_bits rs1
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
def skeleton_utype  (imm : BitVec 20) (rd : regidx) (op : uop) (execute_func : BitVec 20 → BitVec 64 → uop → BitVec 64) : SailM ExecutionResult := do
  let pc ← get_arch_pc () -- states that I modelled this model like this bc its more uniform and neat but made the proof more compilcated
  let result := execute_func imm pc op
  wX_bits rd result
  pure RETIRE_SUCCESS

/-- Given a function `execute_func` with one immediate argument `imm` and a destination register `rd`,
  read the `pc` value and write the result of `execute_func` to the destination register.
-/
def skeleton_utype_auipc  (imm : BitVec 20) (rd : regidx)
    (execute_func : BitVec 20 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let pc ← get_arch_pc ();
  let result := execute_func imm pc
  wX_bits rd result
  pure RETIRE_SUCCESS

/-- Given a function `execute_func` with one immediate argument `imm` and a destination register `rd`,
  write the result of `execute_func` to the destination register.
-/
def skeleton_utype_lui  (imm : BitVec 20) (rd : regidx)
    (execute_func : BitVec 20 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let result := execute_func imm 0#64
  wX_bits rd result
  pure RETIRE_SUCCESS
