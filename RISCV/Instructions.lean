/-! BitVec-only semantics of the RISCV operations. -/

namespace RV64I

/--
  Adds the sign-extended 12-bit immediate to register rs1 and produces the proper sign-extension
  of a 32-bit result in rd. Overflows are ignored and the result is the low 32 bits of the result
  sign-extended to 64 bits. Note, ADDIW rd, rs1, 0 writes the sign-extension of the lower 32 bits
  of register rs1 into register rd (assembler pseudoinstruction SEXT.W).
-/
def addiw (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) rs1_val))

/--
  Build 32-bit constants and uses the U-type format. LUI places the U-immediate value in the top 20
  bits of the destination register rd, filling in the lowest 12 bits with zeros.
-/
def lui (imm : BitVec 20) (_ : BitVec 64) : BitVec 64 :=
    BitVec.signExtend 64 (imm ++ 0x0 : BitVec 12))

/--
  Build pc-relative addresses and uses the U-type format. AUIPC forms a 32-bit offset from the
  20-bit U-immediate, filling in the lowest 12 bits with zeros, adds this offset to the pc,
  then places the result in register rd.
-/
def auipc (imm : BitVec 20) (pc : BitVec 64)  : BitVec 64 :=
  BitVec.add (BitVec.signExtend 64 (BitVec.append imm (0x0 : BitVec 12))) pc 
