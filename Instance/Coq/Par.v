Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Heunen_Vicary.Cartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* * * Par: partial functions over Coq Types / * * Par：Coq 类型上的偏函数 *)

(*
 nLab:      https://ncatlab.org/nlab/show/partial+function
 Wikipedia: https://en.wikipedia.org/wiki/Partial_function

 [Par] is the Kleisli category of the option/Maybe ("partiality", or
 "exception") monad on Coq [Type]s. A partial map A ⇀ B is encoded as a
 total function A → option B, so the homset is

 A ~> B  :=  A → option B,

 with [None] standing for "undefined". Identity is [Some] (the monad's
 [return]) and composition is Kleisli composition (the monad's [bind]),
 i.e. [g ; f := option_bind f ∘ g] threads the "is it None?" check,
 propagating undefinedness. Morphisms are compared pointwise, [∀ x, f x =
 g x] — the extensional equality of partial functions — so this development
 needs no funext axiom (it is closed under the global context).

 This is equivalent (not isomorphic) to the category of pointed sets and
 basepoint-preserving maps: the object [A] realizes the pointed set
 [option A = A ⊔ {None}] with basepoint [None]. 

 --------
 nLab:       https://ncatlab.org/nlab/show/partial+function 
 维基百科:  https://en.wikipedia.org/wiki/Partial_function 

 [Par] 是 Coq [Type] 上选项/Maybe（“部分性”或“异常”）单子（monad）的 Kleisli 范畴。部分映射 A ⇀ B 被编码为全函数 A → option B，因此齐次集为

 A ~> B  :=  A → option B,

 其中 [None] 表示“未定义”。恒等映射是 [Some]（单子的 [return]），组合是 Kleisli 组合（单子的 [bind]），即 [g ; f := option_bind f ∘ g] 处理“是否为 None？”的检查，传播未定义性。态射按点比较，[∀ x, f x = g x]——部分函数的扩展等价——因此这一开发不需要 funext 公理（它在全局上下文下封闭）。这等价于（非同构于）带基点的集合范畴及保持基点的映射：对象 [A] 实现了基点为 [None] 的带基点集合 [option A = A ⊔ {None}]。
*)

Definition option_bind {A B : Type}
           (f : A → option B) (o : option A) : option B :=
  match o with
  | Some x => f x
  | None => None
  end.

Definition option_join {A : Type} (o : option (option A)) : option A :=
  match o with
  | Some x => x
  | None => None
  end.

(* The category of partial maps expressed as functions in Coq. / 在 Coq 中表示为函数的部分映射的范畴。 *)

Program Definition Par : Category := {|
  obj     := Type;
  hom     := fun A B => A ~> option B;
  homset  := fun P Q =>
               {| equiv := fun f g => ∀ x, f x = g x |};
  id      := λ _, Some;
  compose := fun x y z f g => option_bind f ∘ g
|}.
Next Obligation.
  equivalence.
  now rewrite H.
Qed.
Next Obligation.
  proper.
  rewrite H0.
  now destruct (y1 x2); simpl.
Qed.
Next Obligation. now destruct (f x0); simpl. Qed.
Next Obligation. now destruct (h x0); simpl. Qed.
Next Obligation. now destruct (h x0); simpl. Qed.

#[local] Ltac crunch :=
  repeat match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:?; subst
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X eqn:?; subst
  | [ H : Some _ = Some _ |- _ ] => inv H
  | [ H : _ _ = Some _ |- _ ] => rewrite H in *
  end; auto; try discriminate; try tauto.

#[local] Ltac solveit :=
  try unfold option_bind;
  solve [ intuition idtac; simpl; crunch
        | intuition eauto
        | firstorder eauto
        | crunch ].

#[export] Program Instance Par_Monoidal : @Monoidal Par := {
  I := False;
  tensor := {|
    (*
 Tensor of two objects, computed on underlying (non-basepoint) sets.
 On the pointed-set realizations [option x], [option y] this is their
 *cartesian product* with only the basepoint pair [(None, None)]
 removed and re-adjoined as the new basepoint:

 option x × option y  ≅  ((x * y) + x + y) ⊔ {(None, None)}.

 Hence the underlying set is [(x * y) + x + y] (both-defined,
 left-defined, right-defined cases). This is the product in pointed
 sets, NOT the smash product (which would collapse the whole wedge,
 leaving only [x * y]); accordingly Par below is proven cartesian
 monoidal, and the smash product is not cartesian. 

 --------
 两个对象的张量，基于其底层（非基点）集合计算。
 在有基点集合的实现  [option x] 、 [option y] 上，这是它们的
 *笛卡尔积*，仅移除基点对  [(None, None)] 
 并重新作为新的基点加入：

 option x × option y  ≅  ((x * y) + x + y) ⊔ {(None, None)}。

 因此底层集合是  [(x * y) + x + y]  （两者定义的情况、左定义、右定义的情况）。这是有基点集合中的积，而不是 smash 积（smash 积会塌缩整个楔形，仅保留  [x * y] ）；因此下面的 Par 被证明是笛卡尔幺半群，而 smash 积则不是笛卡尔积。
*)
    fobj := λ '(x, y), (x * y) + x + y;
    fmap := λ '(x1, x2) '(y1, y2) '(f1, f2) o,
      match o with
      | Datatypes.inl (Datatypes.inl (x, y)) =>
          match f1 x, f2 y with
          | Some x', Some y' => Some (Datatypes.inl (Datatypes.inl (x', y')))
          | Some x', None => Some (Datatypes.inl (Datatypes.inr x'))
          | None, Some y' => Some (Datatypes.inr y')
          | None, None => None
          end
      | Datatypes.inl (Datatypes.inr x) =>
          match f1 x with
          | Some x' => Some (Datatypes.inl (Datatypes.inr x'))
          | None => None
          end
      | Datatypes.inr y =>
          match f2 y with
          | Some y' => Some (Datatypes.inr y')
          | None => None
          end
      end;
  |};
  unit_left := λ _, {|
    to := λ x,
      match x with
      | Datatypes.inl (Datatypes.inl (H, _)) => False_rect _ H
      | Datatypes.inl (Datatypes.inr H) => False_rect _ H
      | Datatypes.inr x => Some x
      end;
    from := λ x, Some (Datatypes.inr x)
  |};
  unit_right := λ _, {|
    to := λ x,
      match x with
      | Datatypes.inl (Datatypes.inl (_, H)) => False_rect _ H
      | Datatypes.inl (Datatypes.inr x) => Some x
      | Datatypes.inr H => False_rect _ H
      end;
    from := λ x, Some (Datatypes.inl (Datatypes.inr x))
  |};
  tensor_assoc := λ _ _ _, {|
    to   := _;
    from := _;
  |};
}.
Next Obligation.
  proper; simpl in *.
  - now rewrite (H a), (H0 b).
  - now rewrite (H b).
  - now rewrite (H0 b).
Qed.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export] Program Instance Par_BraidedMonoidal : @BraidedMonoidal Par := {
  braid := λ _ _ p,
    match p with
    | Datatypes.inl (Datatypes.inl (x, y)) =>
        Some (Datatypes.inl (Datatypes.inl (y, x)))
    | Datatypes.inl (Datatypes.inr x) => Some (Datatypes.inr x)
    | Datatypes.inr y => Some (Datatypes.inl (Datatypes.inr y))
    end
}.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export] Program Instance Par_BalancedMonoidal : @BalancedMonoidal Par.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export] Program Instance Par_SymmetricMonoidal : @SymmetricMonoidal Par.
Next Obligation. solveit. Defined.

#[export] Program Instance Par_RelevanceMonoidal : @RelevanceMonoidal Par := {
  diagonal := λ _ x, Some (Datatypes.inl (Datatypes.inl (x, x)))
}.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export]
Program Instance Par_SemicartesianMonoidal : @SemicartesianMonoidal Par _ := {
  eliminate := λ _ _, None
}.
Next Obligation.
  destruct (f x0); try tauto.
  destruct (g x0); try tauto.
Defined.

#[export] Program Instance Par_CartesianMonoidal : @CartesianMonoidal Par.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export] Instance Par_Terminal : @Terminal Par :=
  @SemicartesianMonoidal_Terminal _ Par_Monoidal Par_SemicartesianMonoidal.

#[export] Program Instance Par_Cartesian : @Cartesian Par :=
  @CartesianMonoidal_Cartesian _ Par_CartesianMonoidal.

(*
 Par is not cartesian closed.

 It is *also* not closed for the monoidal tensor defined above (the product
 in pointed sets, [(x * y) + x + y]): an earlier [Par_ClosedMonoidal]
 instance has been removed because the iso laws [to_from = id] and
 [from_to = id] for the candidate currying are not provable in general. The
 parallel development in Instance/Sets/Par.v contains a pair of [_impossible]
 lemmas (search "to_from_impossible") that prove the negation under
 decidability/inhabitance assumptions, demonstrating the obstruction. 

 --------
 Par 不是笛卡尔闭的。

 它也不是对上面定义的单体张量封闭的（指点集中的乘积，[(x * y) + x + y]）：一个早期的 [Par_ClosedMonoidal] 实例已被移除，因为候选柯里化的同构定律 [to_from = id] 和 [from_to = id] 通常无法证明。在 Instance/Sets/Par.v 中的并行开发包含一对 [_impossible] 引理（搜索“to_from_impossible”）在可判定性/存在性假设下证明了其否定，展示了这种障碍。
*)

#[export] Program Instance Par_Initial : Initial Par := {
  terminal_obj := False;
  one := λ _ _, False_rect _ _
}.
Next Obligation. contradiction. Qed.

#[export] Program Instance Par_Cocartesian : @Cocartesian Par := {
  product_obj := sum;
  fork := λ _ _ _ f g x,
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  exl  := λ _ _ p, Some (Datatypes.inl p);
  exr  := λ _ _ p, Some (Datatypes.inr p)
}.
Next Obligation.
  split; intros.
  - split; intros;
    rewrite H; reflexivity.
  - destruct x0; firstorder.
Qed.

Open Scope object_scope.
