import LeanRV64D.Sail.Sail
import LeanRV64D.Sail.BitVec
import LeanRV64D

open LeanRV64D.Functions

/-! Monad-free Sail-style specification -/

namespace SailRV64I

def utype (imm : BitVec 20) (pc : BitVec 64) (op : uop)  : BitVec 64 :=
  let off := (sign_extend (m := (2 ^i 3) *i 8) (imm ++ (0x0 : BitVec 12)))
  match op with
  | uop.LUI => off
  | uop.AUIPC => BitVec.add pc off

def shiftiop (shamt : BitVec 6) (op : sop) (rs1_val : BitVec 64) : BitVec 64 :=
  match op with
  | sop.SLLI => (Sail.shift_bits_left rs1_val shamt)
  | sop.SRLI => (Sail.shift_bits_right rs1_val shamt)
  | sop.SRAI => (shift_bits_right_arith rs1_val shamt)

def addiw (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  let result :=  rs1_val + (sign_extend (m := ((2 ^i 3) *i 8)) imm)
  (sign_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb result 31 0))

def shiftiwop (shamt : BitVec 5) (op : sopw) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb (rs1_val) 31 0
  let result : (BitVec 32) :=
    match op with
    | sopw.SLLIW => (Sail.shift_bits_left rs1_val32 shamt)
    | sopw.SRLIW => (Sail.shift_bits_right rs1_val32 shamt)
    | sopw.SRAIW => (shift_bits_right_arith rs1_val32 shamt)
  (sign_extend (m := ((2 ^i 3) *i 8)) result)
