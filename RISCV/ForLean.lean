/-! Lean theorems to be upstreamed. -/

theorem sshiftRight_eq_setWidth_extractLsb_signExtend {w : Nat} (n : Nat) (x : BitVec w) :
    x.sshiftRight n = ((x.signExtend (w + n)).extractLsb (w - 1 + n) n).setWidth w := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_setWidth, BitVec.getLsbD_extract,
    Nat.add_sub_cancel, show i ≤ w - 1 by omega, decide_true, BitVec.getLsbD_signExtend,
    Bool.true_and]
  by_cases hni : (n + i) < w
  <;> (simp [hni]; omega)

theorem extractLsb'_eq_setWidth {x : BitVec w} : x.extractLsb' 0 n = x.setWidth n := by
  ext i hi
  simp


theorem extractLsb'_ofInt_eq_ofInt {x : Int} {w w' : Nat} (h : w ≤ w') :
    (BitVec.extractLsb' 0 w (BitVec.ofInt w' x)) = (BitVec.ofInt w x) := by
  simp only [extractLsb'_eq_setWidth, ← BitVec.signExtend_eq_setWidth_of_le _ (by omega)]
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_signExtend, BitVec.toInt_ofInt, h, Nat.min_eq_left]
  rw [Int.bmod_bmod_of_dvd]
  apply Nat.pow_dvd_pow 2 h

theorem Int.tmod_lt_of_lt (a : Int) {b : Int} (H : a < x) : Int.tmod a b < x := by
  sorry

theorem Int.le_tmod_of_le (a : Int) {b : Int} (H : x ≤ a) : x ≤ Int.tmod a b := by
  sorry
