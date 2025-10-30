import LeanRV64D.Sail.Sail
import LeanRV64D.Sail.BitVec
import LeanRV64D

open LeanRV64D.Functions

/-! Monad-free Sail-style specification -/

namespace SailRV64I

def addiw (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  let result :=  rs1_val + (sign_extend (m := ((2 ^i 3) *i 8)) imm)
  (sign_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb result 31 0))

def utype (imm : (BitVec 20)) (pc : (BitVec 64)) (op : uop)  : BitVec 64 :=
  let off := (sign_extend (m := ((2 ^i 3) *i 8)) (imm ++ (0x000 : (BitVec 12))))
  match op with
  | uop.LUI => off
  | uop.AUIPC => BitVec.add pc off
