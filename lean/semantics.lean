import .syntax

open val bin_op exp instruction

def eval (n m : ℕ) : ∀ (op : bin_op), val
| PlusOp  := VNat (n + m)
| MinusOp := VNat (n - m)
| LeOp    := VBool (n ≤ m)
| LtOp    := VBool (n < m)
| EqOp    := VBool (n = m)

inductive big_step : exp → val → Prop
| RunVal {v} : big_step (EVal v) v
| RunOp {op eₙ eₘ n m}
    (_ : big_step eₙ (VNat n))
    (_ : big_step eₘ (VNat m))
  : big_step (EOp op eₙ eₘ) (eval n m op)
| RunIfT {c t f : exp} {v : val}
    (_ : big_step c (VBool tt))
    (_ : big_step t v)
  : big_step (EIf c t f) v
| RunIfF {c t f : exp} {v : val}
    (_ : big_step c (VBool ff))
    (_ : big_step f v)
  : big_step (EIf c t f) v

infixr ` ⟹ ` : 1 := big_step

def at_least {α : Type} (n : ℕ) : list α → Prop
| (l : list α) := l.length ≥ n

inductive vm_big_step : (list instruction × list val) → list val → Prop
| RunEmpty {stack} : vm_big_step ([], stack) stack
| RunPush {instrs stack res v}
    (_ : vm_big_step (instrs, v :: stack) res)
  : vm_big_step (IPush v :: instrs, stack) res
| RunOpInstr {instrs stack res op} {n m : ℕ} 
    (_ : vm_big_step (instrs, eval n m op :: stack) res)
  : vm_big_step (IOp op :: instrs, VNat n :: VNat m :: stack) res
| RunTBranch {instrs stack res n}
    (_ : at_least n instrs)
    (_ : vm_big_step (instrs, stack) res)
  : vm_big_step (IBranch n :: instrs, VBool tt :: stack) res
| RunFBranch {instrs stack res n}
    (_ : at_least n instrs)
    (_ : vm_big_step (instrs.drop n, stack) res)
  : vm_big_step (IBranch n :: instrs, VBool ff :: stack) res
| RunJump {instrs stack res n}
    (_ : at_least n instrs)
    (_ : vm_big_step (instrs.drop n, stack) res)
  : vm_big_step (IJump n :: instrs, stack) res

infix ` ⟹ᵥₘ ` : 1 := vm_big_step