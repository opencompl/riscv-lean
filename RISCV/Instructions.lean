/-! BitVec-only semantics of the RISCV operations. -/

namespace RV64I

/--
  Build 32-bit constants and uses the U-type format. LUI places the U-immediate value in the top 20
  bits of the destination register rd, filling in the lowest 12 bits with zeros.
-/
def lui (imm : BitVec 20) (_ : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (imm ++ (0x0 : BitVec 12))

/--
  Build pc-relative addresses and uses the U-type format. AUIPC forms a 32-bit offset from the
  20-bit U-immediate, filling in the lowest 12 bits with zeros, adds this offset to the pc,
  then places the result in register rd.
-/
def auipc (imm : BitVec 20) (pc : BitVec 64) : BitVec 64 :=
  BitVec.add (BitVec.signExtend 64 (BitVec.append imm (0x0 : BitVec 12))) pc

/--
  Performs logical left shift on the value in register rs1 by the shift amount held in the lower 5
  bits of the immediate In RV64, bit-25 is used to shamt[5].
-/
def slli (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 := rs1_val <<< shamt

/--
  Performs logical right shift on the value in register rs1 by the shift amount held in the lower 5
  bits of the immediate In RV64, bit-25 is used to shamt[5].
-/
def srli (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 := rs1_val >>> shamt

/--
  Performs arithmetic right shift on the value in register rs1 by the shift amount held in the
  lower 5 bits of the immediate In RV64, bit-25 is used to shamt[5].
-/
def srai (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.sshiftRight' rs1_val shamt)

/--
  Adds the registers rs1 and rs2 and stores the result in rd. Arithmetic overflow is ignored and
  the result is simply the low XLEN bits of the result.
-/
def add (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val + rs2_val

/--
  Subs the register rs2 from rs1 and stores the result in rd. Arithmetic overflow is ignored and
  the result is simply the low XLEN bits of the result.
-/
def sub (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val - rs2_val

/--
  Performs logical left shift on the value in register rs1 by the shift amount held in the lower 5
  bits of register rs2.
-/
def sll (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let shamt := (BitVec.extractLsb 5 0 rs2_val);
  rs1_val <<< shamt

/--
  Place the value 1 in register rd if register rs1 is less than register rs2 when both are treated
  as signed numbers, else 0 is written to rd.
-/
def slt (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.ofBool (BitVec.slt rs1_val rs2_val))

/--
  Place the value 1 in register rd if register rs1 is less than register rs2 when both are treated
  as unsigned numbers, else 0 is written to rd.
-/
def sltu (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.ofBool (BitVec.ult rs1_val rs2_val))

/--
  Performs bitwise XOR on registers rs1 and rs2 and place the result in rd.
-/
def xor (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val ^^^ rs2_val

/--
  Logical right shift on the value in register rs1 by the shift amount held in the lower 5 bits of
  register rs2.
-/
def srl (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let shamt := (BitVec.extractLsb 5 0 rs2_val)
  rs1_val >>> shamt

/--
  Performs arithmetic right shift on the value in register rs1 by the shift amount held in the
  lower 5 bits of register rs2.
-/
def sra (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.sshiftRight' rs1_val (BitVec.extractLsb 5 0 rs2_val)

/--
  Performs bitwise OR on registers rs1 and rs2 and place the result in rd.
-/
def or (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val ||| rs2_val

/--
  Performs bitwise AND on registers rs1 and rs2 and place the result in rd.
-/
def and (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val &&& rs2_val

/--
  Adds the sign-extended 12-bit immediate to register rs1 and produces the proper sign-extension
  of a 32-bit result in rd. Overflows are ignored and the result is the low 32 bits of the result
  sign-extended to 64 bits. Note, ADDIW rd, rs1, 0 writes the sign-extension of the lower 32 bits
  of register rs1 into register rd (assembler pseudoinstruction SEXT.W).
-/
def addiw (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) rs1_val))

/--
  Performs logical left shift on the 32-bit of value in register rs1 by the shift amount held in
  the lower 5 bits of the immediate. Encodings with $imm[5] neq 0$ are reserved.
-/
def slliw (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 ((BitVec.extractLsb' 0 32 rs1_val) <<< shamt)

/--
  Performs logical right shift on the 32-bit of value in register rs1 by the shift amount held in
  the lower 5 bits of the immediate. Encodings with $imm[5] neq 0$ are reserved.
-/
def srliw (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 ((BitVec.extractLsb' 0 32 rs1_val) >>> shamt)

/--
  Performs arithmetic right shift on the 32-bit of value in register rs1 by the shift amount held
  in the lower 5 bits of the immediate. Encodings with $imm[5] neq 0$ are reserved.
-/
def sraiw (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.sshiftRight' (BitVec.extractLsb 31 0 rs1_val) shamt)

/--
  Adds the 32-bit of registers rs1 and 32-bit of register rs2 and stores the result in rd.
  Arithmetic overflow is ignored and the low 32-bits of the result is sign-extended to 64-bits and
  written to the destination register.
-/
def addw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb' 0 32 rs1_val
  let rs2 := BitVec.extractLsb' 0 32 rs2_val
  BitVec.signExtend 64 (BitVec.add rs1 rs2)

/--
  Subtract the 32-bit of registers rs1 and 32-bit of register rs2 and stores the result in rd.
  Arithmetic overflow is ignored and the low 32-bits of the result is sign-extended to 64-bits and
  written to the destination register.
-/
def subw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb' 0 32 rs1_val
  let rs2 := BitVec.extractLsb' 0 32 rs2_val
  BitVec.signExtend 64 (BitVec.sub rs1 rs2)

/--
  Performs logical left shift on the low 32-bits value in register rs1 by the shift amount held in
  the lower 5 bits of register rs2 and produce 32-bit results and written to the destination
  register rd.
-/
def sllw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2 := BitVec.extractLsb' 0 32 rs2_val;
  let shamt := BitVec.extractLsb' 0 5 rs2;
  BitVec.signExtend 64 (rs1 <<< shamt)

/--
  Performs logical right shift on the low 32-bits value in register rs1 by the shift amount held in
  the lower 5 bits of register rs2 and produce 32-bit results and written to the destination
  register rd.
-/
def srlw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2 := BitVec.extractLsb' 0 32 rs2_val;
  let shamt := BitVec.extractLsb' 0 5 rs2;
  BitVec.signExtend 64 (rs1 >>> shamt)

/--
  Performs arithmetic right shift on the low 32-bits value in register rs1 by the shift amount held
  in the lower 5 bits of register rs2 and produce 32-bit results and written to the destination
  register rd.
-/
def sraw (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  let rs1 := BitVec.extractLsb 31 0 rs1_val
  let rs2 := BitVec.extractLsb 4 0 rs2_val
  BitVec.signExtend 64 (BitVec.sshiftRight' rs1 rs2)
