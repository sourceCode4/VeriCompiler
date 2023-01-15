import ..syntax ..semantics ..lovelib

open instruction val bin_op vm_big_step

lemma example1 : 
 vm_big_step
  ([IPush (VNat 10), 
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
  ([IPush (VNat 10), IPush (VBool false), IOp EqOp], []) out :=
begin
  assume hexists,
  cases' hexists,
  repeat { cases' h }
end

lemma example3 : 
  ([IPush (VBool false), 
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
  ¬ ∃ out, ([IBranch n], [VBool false]) ⟹ᵥₘ out :=
begin
  assume n hnz hex,
  cases hex with hout hstep,
  cases hstep; rename hstep__x → hleast,
  cases hleast,
  contradiction
end

