import ..syntax ..semantics ..lovelib

open instruction exp val bin_op big_step vm_big_step

lemma example1 : 
 vm_big_step
  ([], 
   [IPush (VNat 10), 
    IPush (VNat 20), 
    IOp EqOp, 
    IBranch 1, 
    IPush (VNat 1), 
    IPush (VNat 2), 
    IPush (VNat 3)],
  [])
  [VNat 3, VNat 2] :=
begin
  repeat { apply RunPush },
  apply RunOpInstr,
  rw [eval],
  apply RunFBranch,
  { rw [at_least, list.length],
    apply nat.le_add_left },
  repeat { rw [list.drop]},
  repeat { apply RunPush },
  exact RunEmpty
end

lemma example2 : ¬ ∃ out,
 vm_big_step
  ([], [IPush (VNat 10), IPush (VBool false), IOp EqOp], []) out :=
begin
  assume hexists,
  cases' hexists,
  repeat { cases' h }
end

lemma example3 : 
  ([],
   [IPush (VBool false), 
    IBranch 1, 
    IBranch 10,
    IPush (VNat 2),
    IJump 1,
    IPush (VNat 2),
    IPush (VNat 3),
    IOp PlusOp], []) 
  ⟹ᵥₘ [VNat 5] :=
begin
  apply RunPush,
  apply RunFBranch,
  { rw [at_least, list.length], 
    linarith },
  { repeat { rw [list.drop] },
    apply RunPush,
    apply RunJump,
    { rw [at_least, list.length], linarith },
    { repeat { rw [list.drop] },
      apply RunPush,
      apply RunOpInstr,
      exact RunEmpty  
    } 
  }
end

lemma example4 : 
  ∀ n, n ≠ 0 → 
  ¬ ∃ out, ([], [IBranch n], [VBool false]) ⟹ᵥₘ out :=
begin
  assume n hnz hex,
  cases hex with hout hstep,
  cases hstep; rename hstep__x → hleast,
  cases hleast,
  contradiction
end

lemma unbound_var_no_out₁ : 
  ¬ ∃ out, EOp PlusOp (EVal (VNat 0)) (EVar "x") ⟹ out := 
begin
  assume hex,
  cases hex with hval hstep,
  cases hstep,
  cases hstep__x_1
end

lemma unbound_var_no_out₂ : 
  ¬ ∃ out, ELet "y" (EVal (VNat 1)) (EOp PlusOp (EVal (VNat 0)) (EVar "x")) ⟹ out := 
begin
  assume hex,
  cases' hex,
  cases' h,
  repeat {rw subst at h_1},
  rw ite at h_1,
  cases' h_1,
  cases' h_1_1
end

lemma test_name_shadow : 
  ELet "x" (ELet "x" (EVal (VNat 1)) 
              (EOp PlusOp (EVar "x") (EVal (VNat 2)))) -- = 3
    (ELet "x" (EVal (VNat 0)) 
        (EOp EqOp (EVar "x") (EVal (VNat 0)))) ⟹ VBool true :=
begin
  apply RunLet,
  { apply RunLet,
    { apply RunVal },
    { repeat {rw subst},
      apply RunOp,
      simp,
      exact RunVal,
      exact RunVal } },
  { repeat {rw subst},
    simp,
    apply RunLet,
    repeat {apply RunVal},
    repeat {rw subst},
    simp,
    have heq : VBool tt = eval 0 0 EqOp := by refl,
    rw heq,
    apply RunOp,
    exact RunVal,
    exact RunVal
  }
end

lemma test_ext : 
  ([],
   [IPush (VNat 0),
    IPush (VNat 1),
    IOpenScope "x",
    IOpenScope "y",
    IPush (VNat 2),
    ILookup "x",
    ICloseScope,
    IOp PlusOp], []) ⟹ᵥₘ [VNat 3] :=
begin
  apply RunPush,
  apply RunPush,
  apply RunOpenScope,
  apply RunOpenScope,
  apply RunPush,
  apply RunLookup,
  { apply bound.btail,
    finish,
    apply bound.bhead },
  apply RunCloseScope,
  have h : VNat 3 = eval 1 2 PlusOp := by refl,
  rw h,
  apply RunOpInstr,
  exact RunEmpty
end
