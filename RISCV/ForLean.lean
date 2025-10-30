/-! Lean theorems to be upstreamed. -/

theorem sshiftRight_eq_setWidth_extractLsb_signExtend {w : Nat} (n : Nat) (x : BitVec w) :
    x.sshiftRight n = ((x.signExtend (w + n)).extractLsb (w - 1 + n) n).setWidth w := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_setWidth, BitVec.getLsbD_extract,
    Nat.add_sub_cancel, show i ≤ w - 1 by omega, decide_true, BitVec.getLsbD_signExtend,
    Bool.true_and]
  by_cases hni : (n + i) < w
  <;> (simp [hni]; omega)
