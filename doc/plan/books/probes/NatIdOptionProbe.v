(*
PROBE for QA finding E1 (#916): how many natural transformations Id ==> option
   are there on Coq Types?

   #916's Work item 2 orders: "Prove that Nat(Id, (-)+) has exactly ONE element,
   the 'inject' transformation x |-> Some x".  That is FALSE.  Naturality forces
   alpha_X x = fmap x (alpha_unit tt) by probing at the singleton, and
   option unit has TWO inhabitants, so there are exactly two such families:
   Some, and the constant-None family.  This probe exhibits both, proves they
   are natural, and proves they are distinct -- which already refutes "exactly
   one" without needing the full uniqueness argument.

--------
针对 QA 发现 E1 (#916) 的探讨：在 Coq 类型上有多少个自然变换 Id ==> option？

#916 的工作项目 2 要求：“证明 Nat(Id, (-)+) 恰好有一个元素，即 ‘inject’ 变换 x |-> Some x。” 这是错误的。自然性迫使 alpha_X x = fmap x (alpha_unit tt) 通过在单元素集合上探查，而 option unit 有两个元素，因此正好有两类这样的族：Some，以及常量 None 族。该探讨展示了两者，证明它们是自然的，并且证明它们不同——这已经反驳了“恰好一个”的说法，而无需完整的唯一性证明。
*)

Require Import Coq.Init.Datatypes.

Definition nat_trans (F G : Type -> Type) := forall X : Type, F X -> G X.

Definition omap {A B} (f : A -> B) (o : option A) : option B :=
  match o with Some a => Some (f a) | None => None end.

(* Candidate 1: the injection. / 候选人1：注射。 *)
Definition inject : nat_trans (fun X => X) option := fun X x => Some x.

(* Candidate 2: the constant-None family. / 候选人 2：常数-无家族。 *)
Definition constNone : nat_trans (fun X => X) option := fun X _ => None.

(* Both are natural: omap f (alpha_X x) = alpha_Y (f x). / 两者都是自然的：omap f (alpha_X x) = alpha_Y (f x)。 *)
Theorem inject_natural :
  forall (X Y : Type) (f : X -> Y) (x : X), omap f (inject X x) = inject Y (f x).
Proof. reflexivity. Qed.

Theorem constNone_natural :
  forall (X Y : Type) (f : X -> Y) (x : X), omap f (constNone X x) = constNone Y (f x).
Proof. reflexivity. Qed.

(* They are distinct, so Nat(Id, option) has AT LEAST two elements. / 它们是不同的，所以 Nat(Id, option) 至少有两个元素。 *)
Theorem inject_neq_constNone : inject <> constNone.
Proof.
  intro H.
  assert (inject unit tt = constNone unit tt) as HC by (rewrite H; reflexivity).
  simpl in HC. discriminate.
Qed.

(*
The counting engine: option unit has exactly two inhabitants, which is what
   bounds the family count above by two once naturality pins alpha to alpha_unit.

--------
计数引擎：选项单元恰好有两个元素，这就是一旦自然性将 alpha 固定到 alpha_unit 时，家庭数量上界为二的原因。
*)
Theorem option_unit_exactly_two :
  forall o : option unit, o = Some tt \/ o = None.
Proof. intro o. destruct o as [u|]. - left. destruct u. reflexivity. - right. reflexivity. Qed.
