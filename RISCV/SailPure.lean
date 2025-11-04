import LeanRV64D.Sail.Sail
import LeanRV64D.Sail.BitVec
import LeanRV64D

open LeanRV64D.Functions

/-!
  Monad-free Sail-style specification
  Ordered as in https://docs.riscv.org/reference/isa/unpriv/rv64.html
-/

namespace SailRV64I

/-! # RV64I Base Integer Instruction Set -/

def utype (imm : BitVec 20) (pc : BitVec 64) (op : uop) : BitVec 64 :=
  let off := (sign_extend (m := 64) (imm ++ (0x0 : BitVec 12)))
  match op with
  | uop.LUI => off
  | uop.AUIPC => BitVec.add pc off

def addiw (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  let result :=  rs1_val + (sign_extend (m := ((2 ^i 3) *i 8)) imm)
  (sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0))

def shiftiop (shamt : BitVec 6) (op : sop) (rs1_val : BitVec 64) : BitVec 64 :=
  match op with
  | sop.SLLI => (Sail.shift_bits_left rs1_val shamt)
  | sop.SRLI => (Sail.shift_bits_right rs1_val shamt)
  | sop.SRAI => (shift_bits_right_arith rs1_val shamt)

def rtype (op : rop) (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  match op with
  | rop.ADD => rs1_val + rs2_val
  | rop.SUB => rs1_val - rs2_val
  | rop.SLL =>
    (Sail.shift_bits_left rs1_val
        (Sail.BitVec.extractLsb rs2_val (LeanRV64D.Functions.log2_xlen -i 1) 0))
  | rop.SLT => (zero_extend (m := 64) (bool_to_bits (zopz0zI_s rs1_val rs2_val)))
  | rop.SLTU => (zero_extend (m := 64) (bool_to_bits (zopz0zI_u rs1_val rs2_val)))
  | rop.XOR => rs1_val ^^^ rs2_val
  | rop.SRL =>
    (Sail.shift_bits_right rs1_val
        (Sail.BitVec.extractLsb rs2_val (LeanRV64D.Functions.log2_xlen -i 1) 0))
  | rop.SRA =>
    (shift_bits_right_arith rs1_val
        (Sail.BitVec.extractLsb rs2_val (LeanRV64D.Functions.log2_xlen -i 1) 0))
  | rop.OR => rs1_val ||| rs2_val
  | rop.AND => rs1_val &&& rs2_val

def shiftiwop (shamt : BitVec 5) (op : sopw) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb rs1_val 31 0
  let result : BitVec 32 :=
    match op with
    | sopw.SLLIW => (Sail.shift_bits_left rs1_val32 shamt)
    | sopw.SRLIW => (Sail.shift_bits_right rs1_val32 shamt)
    | sopw.SRAIW => (shift_bits_right_arith rs1_val32 shamt)
  (sign_extend (m := 64) result)

def rtypew (op : ropw) (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb rs1_val 31 0
  let rs2_val32 :=  Sail.BitVec.extractLsb rs2_val 31 0
  let result : BitVec 32 :=
    match op with
    | ropw.ADDW => (rs1_val32 + rs2_val32)
    | ropw.SUBW => (rs1_val32 - rs2_val32)
    | ropw.SLLW => (Sail.shift_bits_left rs1_val32 (Sail.BitVec.extractLsb rs2_val32 4 0))
    | ropw.SRLW => (Sail.shift_bits_right rs1_val32 (Sail.BitVec.extractLsb rs2_val32 4 0))
    | ropw.SRAW => (shift_bits_right_arith rs1_val32 (Sail.BitVec.extractLsb rs2_val32 4 0))
  ((sign_extend (m := 64) result))

/-! # M Extension for Integer Multiplication and Division -/

def rem (is_unsigned : Bool) (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_int : Int := if is_unsigned then BitVec.toNat rs1_val else BitVec.toInt rs1_val
  let rs2_int : Int := if is_unsigned then BitVec.toNat rs2_val else BitVec.toInt rs2_val
  let remainder := if (rs2_int == 0 : Bool) then rs1_int else (Int.tmod rs1_int rs2_int)
  to_bits_truncate (l := 64) remainder

def remw (is_unsigned : Bool) (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb rs1_val 31 0
  let rs2_val32 := Sail.BitVec.extractLsb rs2_val 31 0
  let rs1_int : Int := if is_unsigned then BitVec.toNat rs1_val32 else BitVec.toInt rs1_val32
  let rs2_int : Int := if is_unsigned then BitVec.toNat rs2_val32 else BitVec.toInt rs2_val32
  let rem := if ((rs2_int == 0) : Bool) then rs1_int else Int.tmod rs1_int rs2_int
  sign_extend (m := 64) (to_bits_truncate (l := 32) rem)

def mulw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := (Sail.BitVec.extractLsb rs1_val 31 0)
  let rs2_val32 := (Sail.BitVec.extractLsb rs2_val 31 0)
  let rs1_int : Int := (BitVec.toInt rs1_val32)
  let rs2_int : Int := (BitVec.toInt rs2_val32)
  let result32 : BitVec 32 := to_bits_truncate (l := 32) (rs1_int *i rs2_int)
  let result : xlenbits := (sign_extend (m := 64) result32)
  result

def mul  (rs2_val : BitVec 64) (rs1_val : BitVec 64) (mul_op : mul_op) : BitVec 64 :=
  let rs1_int : Int := if mul_op.signed_rs1 then BitVec.toInt rs1_val else BitVec.toNat rs1_val
  let rs2_int : Int := if mul_op.signed_rs2 then BitVec.toInt rs2_val else BitVec.toNat rs2_val
  let result_wide := to_bits_truncate (l := 2 *i LeanRV64D.Functions.xlen) (rs1_int *i rs2_int)
  if (mul_op.high : Bool)
    then Sail.BitVec.extractLsb
      result_wide ((2 *i LeanRV64D.Functions.xlen) -i 1) LeanRV64D.Functions.xlen
    else Sail.BitVec.extractLsb result_wide (LeanRV64D.Functions.xlen -i 1) 0

def div (rs2_val : BitVec 64) (rs1_val : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int : Int := if is_unsigned then BitVec.toNat rs1_val else BitVec.toInt rs1_val
  let rs2_int : Int := if is_unsigned then BitVec.toNat rs2_val else BitVec.toInt rs2_val
  let quotient : Int := if ((rs2_int == 0) : Bool) then (Neg.neg 1)
                  else (Int.tdiv rs1_int rs2_int)
  let quotient : Int :=
    if (((LeanRV64D.Functions.not is_unsigned) && (quotient ≥b (2 ^i (LeanRV64D.Functions.xlen -i 1)))) : Bool)
      then (Neg.neg (2 ^i (LeanRV64D.Functions.xlen -i 1)))
    else quotient
  to_bits_truncate (l := 64) quotient

def divw (rs2_val : BitVec 64) (rs1_val : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb (rs1_val) 31 0
  let rs2_val32 :=  Sail.BitVec.extractLsb (rs2_val) 31 0
  let rs1_int : Int := if is_unsigned then BitVec.toNat rs1_val32 else BitVec.toInt rs1_val32
  let rs2_int : Int := if is_unsigned then BitVec.toNat rs2_val32 else BitVec.toInt rs2_val32
  let quotient : Int := if ((rs2_int == 0) : Bool) then (Neg.neg 1) else (Int.tdiv rs1_int rs2_int)
  let quotient : Int :=
    if (((LeanRV64D.Functions.not is_unsigned) && (quotient ≥b (2 ^i 31))) : Bool)
      then (Neg.neg (2 ^i 31))
    else quotient
  sign_extend (m := ((2 ^i 3) *i 8)) (to_bits_truncate (l := 32) quotient)
