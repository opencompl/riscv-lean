/-! Lean theorems to be upstreamed. -/

theorem BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend {w : Nat} (n : Nat) (x : BitVec w) :
    x.sshiftRight n = ((x.signExtend (w + n)).extractLsb (w - 1 + n) n).setWidth w := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_setWidth, BitVec.getLsbD_extract,
    Nat.add_sub_cancel, show i ≤ w - 1 by omega, decide_true, BitVec.getLsbD_signExtend,
    Bool.true_and]
  by_cases hni : (n + i) < w
  <;> (simp [hni]; omega)

theorem BitVec.extractLsb'_eq_setWidth {x : BitVec w} : x.extractLsb' 0 n = x.setWidth n := by
  ext i hi
  simp

theorem BitVec.extractLsb'_ofInt_eq_ofInt {x : Int} {w w' : Nat} (h : w ≤ w') :
    (BitVec.extractLsb' 0 w (BitVec.ofInt w' x)) = (BitVec.ofInt w x) := by
  simp only [extractLsb'_eq_setWidth, ← BitVec.signExtend_eq_setWidth_of_le _ (by omega)]
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_signExtend, BitVec.toInt_ofInt, h, Nat.min_eq_left]
  rw [Int.bmod_bmod_of_dvd]
  apply Nat.pow_dvd_pow 2 h

theorem BitVec.extractLsb_setWidth_of_lt (x : BitVec w) (hi lo v : Nat) (hilo : lo < hi) (hhi : hi < v):
    BitVec.extractLsb hi lo (BitVec.setWidth v x) = BitVec.extractLsb hi lo x := by
  simp only [BitVec.extractLsb]
  ext k
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth, Bool.and_eq_right_iff_imp,
    decide_eq_true_eq]
  omega

theorem Int.lt_tmod_of_neg (a : Int) {b : Int} (H : b < 0) : b < Int.tmod a b :=
  match a, b, Int.eq_negSucc_of_lt_zero H with
  | Int.ofNat _, _, ⟨n, rfl⟩ => by
    rename_i aas
    apply Int.lt_of_lt_of_le H (@Int.emod_nonneg aas (n + 1) (Int.ofNat_add_one_out n ▸ ((@Int.ofNat_ne_zero n.succ).2 (Nat.succ_ne_zero n))))
  | Int.negSucc _, _, ⟨n, rfl⟩ => Int.negSucc_eq n ▸ by
    rw [Int.negSucc_eq, Int.neg_tmod, Int.tmod_neg, Int.neg_lt_neg_iff]
    apply Int.tmod_lt_of_pos
    have := ((@Int.ofNat_ne_zero n.succ).2 (Nat.succ_ne_zero n))
    omega

theorem Int.tmod_lt_of_neg (a : Int) {b : Int} (H : b < 0) : Int.tmod a b < -b :=
  match a, b, Int.eq_negSucc_of_lt_zero H with
  | Int.ofNat _, _, ⟨n, rfl⟩ => by
    rename_i aas
    simp only [tmod, Nat.succ_eq_add_one, ofNat_eq_coe, natCast_emod, natCast_add, cast_ofNat_Int,
      neg_negSucc]
    norm_cast
    apply Nat.mod_lt
    omega
  | Int.negSucc _, _, ⟨n, rfl⟩ => by
    simp only [tmod, Nat.succ_eq_add_one, ofNat_eq_coe, natCast_emod, natCast_add, cast_ofNat_Int,
      neg_negSucc]
    norm_cast
    omega

theorem Int.emod_lt_of_lt {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (hax : a < x) : a % b < x := by
  by_cases hb : b = 0; subst hb; simp [hax]
  have := @Int.emod_lt a b hb
  by_cases hb_lt_x : b < x
  · omega
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

@[simp]
theorem BitVec.ofInt_toInt_tmod_toInt {x y : BitVec w} :
    (BitVec.ofInt w (x.toInt.tmod y.toInt)).toInt = x.toInt.tmod y.toInt := by
  by_cases hb : y.toInt = 0; simp [hb]

  have ylt := @BitVec.two_mul_toInt_lt w y
  have ley := @BitVec.le_two_mul_toInt w y

  rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le_mul_two]
  · by_cases hy : 0 < y.toInt
    · have := Int.lt_tmod_of_pos x.toInt hy
      norm_cast at *
      omega
    · have := @Int.lt_tmod_of_neg x.toInt y.toInt (by omega)
      norm_cast at *
      omega
  · by_cases hy : 0 < y.toInt
    · have := Int.tmod_lt_of_pos x.toInt hy
      norm_cast at *
      omega
    · have := @Int.tmod_lt_of_neg x.toInt y.toInt (by omega)
      norm_cast at *
      omega

theorem BitVec.setWidth_signExtend_eq_self {w w' : Nat} {x : BitVec w} (h : w ≤ w') : (x.signExtend w').setWidth w = x := by
  ext i hi
  simp  [hi, BitVec.getLsbD_signExtend]
  omega
