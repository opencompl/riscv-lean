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

def itype (imm : BitVec 12) (rs1_val : BitVec 64) (op : iop) : BitVec 64 :=
  let immext : xlenbits := (sign_extend (m := 64) imm)
  match op with
  | iop.ADDI => rs1_val + immext
  | iop.SLTI => zero_extend (m := 64) (bool_to_bits (zopz0zI_s rs1_val immext))
  | iop.SLTIU => zero_extend (m := 64) (bool_to_bits (zopz0zI_u rs1_val immext))
  | iop.ANDI =>  rs1_val &&& immext
  | iop.ORI => rs1_val ||| immext
  | iop.XORI => rs1_val ^^^ immext

def addiw (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  let result := rs1_val + (sign_extend (m := ((2 ^i 3) *i 8)) imm)
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

def mul (rs2_val : BitVec 64) (rs1_val : BitVec 64) (mul_op : mul_op) : BitVec 64 :=
  mult_to_bits_half (l := 64) mul_op.signed_rs1 mul_op.signed_rs2 rs1_val rs2_val
      mul_op.result_part

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
  sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)

/-! # "B" Extension for Bit Manipulation -/

/-! ## Zba: Address generation -/

def zba_rtypeuw (rs2 : BitVec 64) (rs1 : BitVec 64) (shamt : BitVec 2) : BitVec 64 :=
  (Sail.shift_bits_left (zero_extend (m := 64) (Sail.BitVec.extractLsb rs1 31 0)) shamt) + rs2

def zba_rtype (rs2 : BitVec 64) (rs1 : BitVec 64) (shamt : BitVec 2) : BitVec 64 :=
  (Sail.shift_bits_left rs1 shamt) + rs2

/-! ## Zbb: Basic bit-manipulation -/

def zbb_rtype (rs2_val : BitVec 64) (rs1_val : BitVec 64) (op : brop_zbb) : BitVec 64 :=
  match op with
  | .ANDN => rs1_val &&& (Complement.complement rs2_val)
  | .ORN => rs1_val ||| (Complement.complement rs2_val)
  | .XNOR => Complement.complement (rs1_val ^^^ rs2_val)
  | .MAX => if ((zopz0zK_s rs1_val rs2_val) : Bool) then rs1_val else rs2_val
  | .MAXU => if ((zopz0zK_u rs1_val rs2_val) : Bool) then rs1_val else rs2_val
  | .MIN => if ((zopz0zI_s rs1_val rs2_val) : Bool) then rs1_val else rs2_val
  | .MINU => if ((zopz0zI_u rs1_val rs2_val) : Bool) then rs1_val else rs2_val
  | .ROL => rotate_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 5 0)
  | .ROR => rotate_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 5 0)

def zbb_rtypew (rs2_val : BitVec 64) (rs1_val : BitVec 64) (op : bropw_zbb) : BitVec 64 :=
  let shamt := Sail.BitVec.extractLsb (rs2_val) 4 0
  let result : (BitVec 32) :=
    match op with
    | bropw_zbb.ROLW => rotate_bits_left rs1_val shamt
    | bropw_zbb.RORW => rotate_bits_right rs1_val shamt
  sign_extend (m := 64) result

def zbb_extop (rs1_val : BitVec 64) (op : extop_zbb) : BitVec 64 :=
  match op with
  | .SEXTB => sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 7 0)
  | .SEXTH => sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 15 0)
  | .ZEXTH => zero_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 15 0)

def zbb_clz (rs1 : BitVec 64) : BitVec 64 :=
  to_bits (l := 64) (Sail.BitVec.countLeadingZeros rs1)

def zbb_clzw (rs1 : BitVec 64) : BitVec 64 :=
  to_bits (l := 64) (Sail.BitVec.countLeadingZeros (Sail.BitVec.extractLsb rs1 31 0))

def zbb_ctz (rs1 : BitVec 64) : BitVec 64 :=
  to_bits (l := 64) (Sail.BitVec.countTrailingZeros rs1)

def zbb_ctzw (rs1 : BitVec 64) : BitVec 64 :=
  to_bits (l := 64) (Sail.BitVec.countTrailingZeros (Sail.BitVec.extractLsb rs1 31 0))

def zbb_roriw (shamt : BitVec 5) (rs1 : BitVec 64) :=
  sign_extend (m := 64) (rotate_bits_right (Sail.BitVec.extractLsb rs1 31 0) shamt)

def zbb_rori (shamt : BitVec 6) (rs1 : BitVec 64) :=
  let shamt := (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)
  rotate_bits_right rs1 shamt

/-! ## Zbc: Carry-less multiplication -/

/-! ## Zbs: Single-bit instructions -/

def zbs_rtype (rs2_val : BitVec 64) (rs1_val : BitVec 64) (op : brop_zbs) : BitVec 64 :=
  let mask : xlenbits :=
    (Sail.shift_bits_left (zero_extend (m := 64) (0b1 : (BitVec 1)))
      (Sail.BitVec.extractLsb rs2_val 5 0))
  let result : xlenbits :=
    match op with
    | .BCLR => (rs1_val &&& (Complement.complement mask))
    | .BEXT => (zero_extend (m := 64) (bool_to_bits (bne (rs1_val &&& mask) (zeros (n := 64)))))
    | .BINV => (rs1_val ^^^ mask)
    | .BSET => (rs1_val ||| mask)
  result

def zbs_iop (shamt : BitVec 6) (rs1_val : BitVec 64) (op : biop_zbs) : BitVec 64 :=
  let mask : xlenbits := (Sail.shift_bits_left (zero_extend (m := 64) (0b1 : (BitVec 1))) shamt)
  let result : xlenbits :=
    match op with
    | .BCLRI => (rs1_val &&& (Complement.complement mask))
    | .BEXTI => (zero_extend (m := 64) (bool_to_bits (bne (rs1_val &&& mask) (zeros (n := 64)))))
    | .BINVI => (rs1_val ^^^ mask)
    | .BSETI => (rs1_val ||| mask)
  result

/-! ## Zbkb: Bit-manipulation for Cryptography-/

def zbkb_rtype (rs2_val : BitVec 64) (rs1_val : BitVec 64) (op : brop_zbkb) : BitVec 64 :=
  match op with
  | .PACK => (Sail.BitVec.extractLsb rs2_val ((LeanRV64D.Functions.xlen_bytes *i 4) -i 1) 0) ++
              (Sail.BitVec.extractLsb rs1_val ((LeanRV64D.Functions.xlen_bytes *i 4) -i 1) 0)
  | .PACKH => zero_extend (m := 64)
              ((Sail.BitVec.extractLsb rs2_val 7 0) ++ (Sail.BitVec.extractLsb rs1_val 7 0))

def zbkb_packw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let result := ((Sail.BitVec.extractLsb rs2_val 15 0) ++ (Sail.BitVec.extractLsb rs1_val 15 0))
  sign_extend (m := 64) result

/-! ## Zbkc: Carry-less multiplication for Cryptography -/

/-! ## Zbkx: Carry-less multiplication for Cryptography -/
