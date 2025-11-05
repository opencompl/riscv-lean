import Batteries.Lean.EStateM
import RISCV.SailPure

open LeanRV64D.Functions

def rX_pure (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) (x : regidx) : BitVec 64 := sorry

@[simp]
theorem run_eq :
    EStateM.run (rX_bits rs2) s = EStateM.Result.ok (rX_pure s rs2) s := by sorry
