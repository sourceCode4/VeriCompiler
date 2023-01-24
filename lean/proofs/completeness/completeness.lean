import .lemmas

open big_step vm_big_step env_big_step val bin_op exp instruction

lemma compile_complete_nv 
  {E : list (string × val)} {e : exp} {r : val} {S : list val} :
    (E, compile e, S) ⟹ₙᵥ (E, r :: S)
  → e ⟹ r :=
begin
  --  assume hp,
  assume hnval,
  sorry
end
