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

theorem Int.lt_tmod_of_neg (a : Int) {b : Int} (H : b < 0) : b < Int.tmod a b :=
  match a, b, Int.eq_negSucc_of_lt_zero H with
  | Int.ofNat _, _, ⟨n, rfl⟩ => by
    rename_i aas
    apply Int.lt_of_lt_of_le H (@Int.emod_nonneg aas (n + 1) (Int.ofNat_add_one_out n ▸ ((@Int.ofNat_ne_zero n.succ).2 (Nat.succ_ne_zero n))))
  | Int.negSucc _, _, ⟨n, rfl⟩ => Int.negSucc_eq n ▸ by
    rw [Int.negSucc_eq, Int.neg_tmod, Int.tmod_neg, Int.neg_lt_neg_iff]
    apply Int.tmod_lt_of_pos
    have :=  ((@Int.ofNat_ne_zero n.succ).2 (Nat.succ_ne_zero n))
    omega

theorem Int.tmod_lt_of_neg (a : Int) {b : Int} (H : b < 0) : Int.tmod a b < -b :=
  match a, b, Int.eq_negSucc_of_lt_zero H with
  | Int.ofNat _, _, ⟨n, rfl⟩ => by
    rename_i aas
    simp
    simp [Int.tmod]
    simp at *
    norm_cast
    apply Nat.mod_lt
    omega
  | Int.negSucc _, _, ⟨n, rfl⟩ => by
    simp [Int.tmod]
    norm_cast
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

theorem BitVec.ofInt_toInt_tmod_toInt {x y : BitVec w} :
    (BitVec.ofInt w (x.toInt.tmod y.toInt)).toInt = x.toInt.tmod y.toInt := by
  rw [BitVec.toInt_ofInt]
  by_cases hb : y.toInt = 0
  · simp [hb]

  have xlt := @BitVec.two_mul_toInt_lt w x
  have ylt := @BitVec.two_mul_toInt_lt w y
  have lex := @BitVec.le_two_mul_toInt w x
  have ley := @BitVec.le_two_mul_toInt w y

  rw [Int.bmod_eq_of_le_mul_two]
  <;> simp
  · by_cases hy : 0 < y.toInt
    · have := @Int.lt_tmod_of_pos x.toInt y.toInt hy
      omega
    · have := @Int.lt_tmod_of_neg x.toInt y.toInt (by omega)
      omega
  · by_cases hy : 0 < y.toInt
    · have := @Int.tmod_lt_of_pos x.toInt y.toInt hy
      omega
    · have := @Int.lt_tmod_of_neg x.toInt y.toInt (by omega)
      have : x.toInt.tmod y.toInt < -y.toInt := @Int.tmod_lt_of_neg x.toInt y.toInt (by omega)
      norm_cast at *
      omega
