-- Source language

inductive val : Type
| VBool : bool → val
| VNat : nat → val

inductive bin_op : Type
| PlusOp : bin_op
| MinusOp : bin_op
| LeOp : bin_op
| LtOp : bin_op
| EqOp : bin_op

inductive exp : Type
| EVal : val → exp
| EOp : bin_op → exp → exp → exp
| EIf : exp → exp → exp → exp

-- Target language

inductive instruction : Type
| IPush : val → instruction   -- push val on stack
| IOp : bin_op → instruction  -- pop two vals, do op, push result
| IBranch : nat → instruction -- pop a bool, continue if true, else skip n instructions
| IJump : nat → instruction   -- skip n instructions