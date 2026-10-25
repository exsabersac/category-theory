(*
AUDIT PROBE for defect S8.

   Claim under test: in Theory/Metacategory.v the predicate

     identity (u : arr) := (forall f, composite f u f) /\ (forall g, composite u g g)

   is UNSATISFIABLE, because [arr := nat] is infinite while [pairs : M.t arr]
   is a finite map.  If so, [FromArrows]'s object type [exists i, identity M i]
   is uninhabited and [Three := FromArrows ThreeArrows] is the EMPTY category.

   The campaign reported it could not build a probe because [Metacategory] is a
   module functor never instantiated outside its own file.  It CAN be
   instantiated: the functor takes any [WSfun PNN], and [FMapWeakList.Make PNN]
   is one.

--------
审计探针用于缺陷 S8。

   测试声明：在 Theory/Metacategory.v 中，谓词

     identity (u : arr) := (forall f, composite f u f) /\ (forall g, composite u g g)

   是不可满足的，因为 [arr := nat] 是无限的，而 [pairs : M.t arr] 是一个有限映射。如果是这样，[FromArrows] 的对象类型 [exists i, identity M i] 是无占用的，而 [Three := FromArrows ThreeArrows] 是空类别。

   报告指出无法构建探针，因为 [Metacategory] 是一个模块函子，从未在自身文件之外实例化。但它是可以被实例化的：该函子接受任何 [WSfun PNN]，而 [FMapWeakList.Make PNN] 就是一个。
*)

From Coq Require Import FMapWeakList.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
From Coq Require Import SetoidList.
Import ListNotations.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Metacategory.

(* Instantiate the functor the file never applies. / 实例化文件从未应用的函子。 *)
Module MyMap := FMapWeakList.Make PNN.
Module Import MC := Metacategory MyMap.

Section S8.

Local Open Scope nat_scope.

(* A bound strictly above every first-coordinate of a key occurring in l. / 严格大于 l 中出现的键的每个第一坐标的界。 *)
Definition keybound (l : list ((nat * nat) * nat)) : nat :=
  S (fold_right (fun p acc => Nat.max (fst (fst p)) acc) 0%nat l).

Lemma keybound_gt : forall l p, In p l -> fst (fst p) < keybound l.
Proof.
  unfold keybound; induction l as [|q l IH]; simpl; intros p Hin.
  - contradiction.
  - destruct Hin as [->|Hin].
    + lia.
    + specialize (IH p Hin). unfold keybound in IH. lia.
Qed.

(* THE MAIN CLAIM: no arrow of any metacategory satisfies [identity]. / 主要声明：没有任何元类别的箭头满足 [identity]。 *)
Theorem identity_unsatisfiable (M : Metacategory) (u : arr M) :
  identity M u -> False.
Proof.
  intros [Hl _].
  set (l := MyMap.elements (pairs M)).
  set (n := keybound l).
  (* [identity] demands a binding for EVERY f, in particular for f = n. / [identity] 要求对每个 f 都有一个绑定，特别是对于 f = n。 *)
  assert (HM : MyMap.MapsTo (n, u) n (pairs M)) by exact (Hl n).
  apply MyMap.elements_1 in HM.
  (* ... but n exceeds every first-coordinate present in the finite [elements]. / ...但是 n 超过有限 [elements] 中存在的每一个第一坐标。 *)
  apply SetoidList.InA_alt in HM.
  destruct HM as [p [Heq Hin]].
  destruct p as [[a b] c].
  destruct Heq as [Hk _]; simpl in Hk.
  assert (Hlt : a < n) by (apply (keybound_gt l (a, b, c)); exact Hin).
  (* PNN.eq is Logic.eq, so the key of p really is (n, u). / PNN.eq 是 Logic.eq，所以 p 的键确实是 (n, u)。 *)
  assert (Hk' : (n, u) = (a, b)) by exact Hk.
  inversion Hk' as [[Hna Hub]].
  lia.
Qed.

(* Consequence 1: the object type of every [FromArrows] category is empty. / 后果 1：每个 [FromArrows] 类别的对象类型都是空的。 *)
Theorem FromArrows_no_objects (M : Metacategory) : @obj (FromArrows M) -> False.
Proof.
  intros [i Hi]; exact (identity_unsatisfiable M i Hi).
Qed.

(*
Consequence 2: [Three] -- presented in the header as the three-object
   category -- has NO objects at all.

--------
后果 2：[Three] —— 在标题中呈现为三对象类别 —— 实际上根本没有任何对象。
*)
Theorem Three_is_empty : @obj Three -> False.
Proof. exact (FromArrows_no_objects ThreeArrows). Qed.

End S8.

(* ---- ex3.10 OVERTURN adjudication: is the surviving content NON-VACUOUS? ---- / ---- ex3.10 推翻裁决：存留内容是非空的吗？ ---- *)
Section Ex310.
Local Open Scope nat_scope.

(*
The table really is inhabited: generator 3 : 1 -> 0, generator 4 : 2 -> 1,
   and the composite 5 = 3 o 4.  So composition_law is not vacuously satisfied.

--------
这个表格确实是有生效的：生成元 3 : 1 -> 0，生成元 4 : 2 -> 1，复合 5 = 3 o 4。因此，组合律不是虚空满足的。
*)
Example tbl_0_3 : composite ThreeArrows 0 3 3.
Proof. apply MyMap.find_2. vm_compute. reflexivity. Qed.

Example tbl_3_4 : composite ThreeArrows 3 4 5.
Proof. apply MyMap.find_2. vm_compute. reflexivity. Qed.

Example tbl_4_2 : composite ThreeArrows 4 2 4.
Proof. apply MyMap.find_2. vm_compute. reflexivity. Qed.

(* composition_law fires on a genuine composable triple: real, non-vacuous content. / composition_law fires on a genuine composable triple: real, non-vacuous content. / 组合律作用于一个真实可组合的三元组：真实、非空内容。 *)
Definition composition_law_live :=
  composition_law ThreeArrows 3 4 2 5 4 tbl_3_4 tbl_4_2.

End Ex310.

Print Assumptions identity_unsatisfiable.
Print Assumptions Three_is_empty.
Print Assumptions composition_law_live.
