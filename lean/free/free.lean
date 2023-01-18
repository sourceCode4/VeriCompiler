import ..syntax

open exp

inductive free (x : string) : ℕ → exp → Prop
| FZero {v} : free 0 (EVal v)
| FOne {v} : free 1 (EVar v)
| FOp {op e₁ e₂ n m} 
  : free n e₁ → free m e₂ 
  → free (n + m) (EOp op e₁ e₂)
| FIf {c t f n m k}
  : free n c → free m t → free k f
  → free (n + m + k) (EIf c t f)
| FLet {v e b n m}
  : v ≠ x → free n e → free m b
  → free (n + m) (ELet v e b)
| FLetShdw {v e b n}
  : v = x → free n e
  → free n (ELet v e b)

open free

def count_free (x : string) : exp → ℕ := sorry

lemma count_correct (v : string) (e : exp) {n} : 
  free v n e ↔ count_free v e = n := sorry