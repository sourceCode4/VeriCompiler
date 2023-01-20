import .syntax .lovelib

open val bin_op exp instruction

def eval (n m : ℕ) : ∀ (op : bin_op), val
| PlusOp  := VNat (n + m)
| MinusOp := VNat (n - m)
| LeOp    := VBool (n ≤ m)
| LtOp    := VBool (n < m)
| EqOp    := VBool (n = m)

def subst (v : val) (x : string) : exp → exp
|   (EVar y) := if x = y then (EVal v) else (EVar y)
| l@(ELet y e body) :=
      if x = y then ELet y (subst e) body
      else ELet y (subst e) (subst body)
| (EIf c t e) := EIf (subst c) (subst t) (subst e)
| (EOp op e₁ e₂) := EOp op (subst e₁) (subst e₂)
| (EVal v) := (EVal v)

def vm_subst' (v : val) (x : string)
  : list string → list instruction → list instruction
| nv [] := []
| nv (ILookup var :: ins) := (if var = x ∧ x ∉ nv then IPush v else ILookup var) :: vm_subst' nv ins
| nv (IOpenScope var :: ins) := IOpenScope var :: vm_subst' (var :: nv) ins
| nv (ICloseScope :: ins) := ICloseScope :: vm_subst' nv.tail ins
| nv (i :: ins) := i :: vm_subst' nv ins

def vm_subst (v : val) (x : string)
  : list instruction → list instruction := vm_subst' v x []

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
| RunLet {e body : exp} {x : string} {v r : val}
  (_ : big_step e v)
  (_ : big_step (subst v x body) r)
  : big_step (ELet x e body) r

infixr ` ⟹ ` : 30 := big_step

def at_least {α : Type} (n : ℕ) : list α → Prop
| (l : list α) := l.length ≥ n

inductive bound : string → val → list (string × val) → Prop
| bhead {x v env}     : bound x v ((x, v) :: env)
| btail {x y v u env} : x ≠ y → bound x v env → bound x v (⟨y, u⟩ :: env)

inductive vm_big_step : 
  list (string × val) × list instruction × list val → list val → Prop
| RunEmpty {env stack} : vm_big_step (env, [], stack) stack
| RunPush {env instrs stack res v}
    (_ : vm_big_step (env, instrs, v :: stack) res)
  : vm_big_step (env, IPush v :: instrs, stack) res
| RunOpInstr {env instrs stack res op} {n m : ℕ} 
    (_ : vm_big_step (env, instrs, eval n m op :: stack) res)
  : vm_big_step (env, IOp op :: instrs, VNat n :: VNat m :: stack) res
| RunTBranch {env instrs stack res n}
    (_ : vm_big_step (env, instrs, stack) res)
  : vm_big_step (env, IBranch n :: instrs, VBool tt :: stack) res
| RunFBranch {env instrs stack res n}
    (_ : at_least n instrs)
    (_ : vm_big_step (env, instrs.drop n, stack) res)
  : vm_big_step (env, IBranch n :: instrs, VBool ff :: stack) res
| RunJump {env instrs stack res n}
    (_ : at_least n instrs)
    (_ : vm_big_step (env, instrs.drop n, stack) res)
  : vm_big_step (env, IJump n :: instrs, stack) res
| RunLookup {env x v instrs stack res}
  (_ : bound x v env)
  (_ : vm_big_step (env, instrs, v :: stack) res)
 : vm_big_step (env, ILookup x :: instrs, stack) res
| RunOpenScope {env x v instrs stack res}
  (_ : vm_big_step (⟨x, v⟩ :: env, instrs, stack) res)
  : vm_big_step (env, IOpenScope x :: instrs, v :: stack) res
| RunCloseScope {env x v instrs stack res}
  (_ : vm_big_step (env, instrs, stack) res)
  : vm_big_step (⟨x, v⟩ :: env, ICloseScope :: instrs, stack) res

infix ` ⟹ᵥₘ ` : 25 := vm_big_step

-- big-step semantics including resulting environment
inductive env_big_step :
    list (string × val) × list instruction × list val 
  → list (string × val) × list val → Prop
| ERunEmpty {env stack} : env_big_step (env, [], stack) (env, stack) 
| ERunPush {env instrs stack res v}
    (_ : env_big_step (env, instrs, v :: stack) res)
  : env_big_step (env, IPush v :: instrs, stack) res
| ERunOpInstr {env instrs stack res op} {n m : ℕ} 
    (_ : env_big_step (env, instrs, eval n m op :: stack) res)
  : env_big_step (env, IOp op :: instrs, VNat n :: VNat m :: stack) res
| ERunTBranch {env instrs stack res n}
    (_ : env_big_step (env, instrs, stack) res)
  : env_big_step (env, IBranch n :: instrs, VBool tt :: stack) res
| ERunFBranch {env instrs stack res n}
    (_ : at_least n instrs)
    (_ : env_big_step (env, instrs.drop n, stack) res)
  : env_big_step (env, IBranch n :: instrs, VBool ff :: stack) res
| ERunJump {env instrs stack res n}
    (_ : at_least n instrs)
    (_ : env_big_step (env, instrs.drop n, stack) res)
  : env_big_step (env, IJump n :: instrs, stack) res
| ERunLookup {env x v instrs stack res}
  (_ : bound x v env)
  (_ : env_big_step (env, instrs, v :: stack) res)
 : env_big_step (env, ILookup x :: instrs, stack) res
| ERunOpenScope {env x v instrs stack res}
  (_ : env_big_step (⟨x, v⟩ :: env, instrs, stack) res)
  : env_big_step (env, IOpenScope x :: instrs, v :: stack) res
| ERunCloseScope {env x v instrs stack res}
  (_ : env_big_step (env, instrs, stack) res)
  : env_big_step (⟨x, v⟩ :: env, ICloseScope :: instrs, stack) res

infix ` ⟹ₙᵥ ` : 25 := env_big_step