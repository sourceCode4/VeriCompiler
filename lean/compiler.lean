import .syntax

open val bin_op exp instruction

def compile : exp → list instruction
| (EVal v) := [IPush v]
| (EOp op e₁ e₂) := compile e₂ ++ compile e₁ ++ [IOp op]
| (EIf c t f) := 
  let t_branch : list instruction := compile t,
      f_branch : list instruction := compile f in
  compile c ++ 
  (IBranch (t_branch.length + 1) :: t_branch) ++ 
  (IJump (f_branch.length) :: f_branch)