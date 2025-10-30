/-! BitVec-only semantics of the RISCV operations. -/

namespace RV64I

def addiw (imm : (BitVec 12)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) rs1_val))
