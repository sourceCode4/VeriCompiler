import .free ..semantics ..lovelib

lemma zero_free_subst_id {e x v} :
  free x 0 e → subst v x e = e :=
begin
  assume h,
  induction' h,
  case FZero { rw subst },
  case FOp { 
    rw subst,
    have hnz : n = 0 := by linarith,
    have hmz : m = 0 := by linarith,
    rw [ih_h hnz, ih_h_1 hmz] },
  case FIf {
    rw subst,
    have hnz : n = 0 := by linarith,
    have hmz : m = 0 := by linarith,
    have hkz : k = 0 := by linarith,
    rw [ih_h hnz, ih_h_1 hmz, ih_h_2 hkz]
  },
  case FLet {
    rw [subst],
    rw if_neg (ne.symm h),
    have hnz : n = 0 := by linarith,
    have hmz : m = 0 := by linarith,
    rw [ih_h_1 hnz, ih_h_2 hmz]
  },
  case FLetShdw {
    rw [subst, if_pos (eq.symm h), ih]
  }
end

lemma subst_zero_free {e x v} : 
  free x 0 (subst v x e) :=
begin
  sorry
end