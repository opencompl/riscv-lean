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

theorem lt_tmod_of_neg (a : Int) {b : Int} (H : b < 0) : b < Int.tmod a b :=
  match a, b, Int.eq_negSucc_of_lt_zero H with
  | Int.ofNat _, _, ⟨n, rfl⟩ => by
    rename_i aas
    apply Int.lt_of_lt_of_le H (@Int.emod_nonneg aas (n + 1) (Int.ofNat_add_one_out n ▸ ((@Int.ofNat_ne_zero n.succ).2 (Nat.succ_ne_zero n))))
  | Int.negSucc _, _, ⟨n, rfl⟩ => Int.negSucc_eq n ▸ by
    rw [Int.negSucc_eq, Int.neg_tmod, Int.tmod_neg, Int.neg_lt_neg_iff]
    apply Int.tmod_lt_of_pos
    have :=  ((@Int.ofNat_ne_zero n.succ).2 (Nat.succ_ne_zero n))
    omega

theorem Int.emod_lt_of_lt (a : Int) {b : Int} (hax : a < x) (ha : 0 ≤ a) (hb : 0 ≤ b) : a % b < x := by
  by_cases hb : b = 0
  · subst hb
    simp [hax]

  have := @Int.emod_lt a b hb

  by_cases hb_lt_x : b < x
  · rw [Int.natAbs_of_nonneg (by omega)] at this
    omega
  · simp at hb_lt_x
    have hab : a < b := by omega
    by_cases ha : 0 ≤ a
    · rw [Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    · simp at *
      rw [Int.emod_eq_of_lt]
      omega
      omega
      omega

theorem Int.tmod_lt_of_lt (a : Int) {b : Int} (H : a < x) (hb : 0 ≤ b): Int.tmod a b < x := by
  rw [Int.tmod_eq_emod]
  split
  ·
    simp
    rename_i h
    cases h
    ·
      rename_i aa
      apply Int.emod_lt_of_lt
      exact H
      exact aa
      exact hb
    ·
      rename_i ab_dvd
      sorry
  ·
    rename_i h
    simp at *



      sorry

theorem Int.tmod_lt_of_lt (a : Int) {b : Int} (H : a < x) : Int.tmod a b < x := by
  rw [Int.tmod_eq_emod]
  split
  ·
    simp
    rename_i h
    cases h
    ·
      rename_i aa
      apply Int.emod_lt_of_lt
      exact H
      exact aa
      exact
      sorry


    split

    have := Int.emod_lt

  obtain (hx|hx|hx) := Int.lt_trichotomy b x
  · sorry
  ·
    simp [H]
  ·
    have := Int.tmod_lt_of_pos a hx




theorem Int.le_tmod_of_le (a : Int) {b : Int} (H : x ≤ a) : x ≤ Int.tmod a b := by
  sorry
