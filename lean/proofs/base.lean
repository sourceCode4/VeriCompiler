import ..semantics ..lovelib

lemma bound_eq {x v u env} : 
  bound x u ((x, v) :: env) ↔ v = u :=
begin
  apply iff.intro,
  { assume h,
    induction' h,
    { refl },
    { contradiction } },
  { assume h,
    rw h,
    apply bound.bhead }
end

lemma eq_if_bound_to_same_name {x v u env} : 
    bound x v env → bound x u env 
  → v = u :=
begin
  assume h1 h2,
  induction' h1,
  { cases' h2, refl, contradiction },
  { cases' h2, contradiction, exact ih h2 }
end