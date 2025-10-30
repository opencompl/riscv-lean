import LeanRV64D.Sail.Sail
import LeanRV64D.Sail.BitVec
import LeanRV64D

open LeanRV64D.Functions

/-!
  We define a BitVec-only semantics of the Sail model, that can decouple from the Sail monad.

-/

namespace SailRV64I

def addiw (imm : (BitVec 12)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let result :=  rs1_val + (sign_extend (m := ((2 ^i 3) *i 8)) imm)
  (sign_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb result 31 0))
