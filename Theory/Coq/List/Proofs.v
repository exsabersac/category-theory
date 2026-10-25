Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.

Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.List.
Require Import Category.Theory.Coq.Maybe.

Generalizable All Variables.

(** Proofs and lemmas for the Coq list instance / Coq 列表实例的证明和引理 *)

(*
nLab: https://ncatlab.org/nlab/show/list+monad
   nLab: https://ncatlab.org/nlab/show/free+monoid
   Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

   This file collects lemmas about the list type whose functor, applicative
   and monad instances live in the parent module [Theory.Coq.List].  The list
   type is the underlying set of the free monoid on A, with [app] as the
   monoid multiplication and [[]] as its unit; the [Forall_append] lemma below
   witnesses that the predicate [Forall P] respects this multiplication.

   The remaining lemmas in this range ([olast_*], [Forall_ordered],
   [StronglySorted_*]) are pure list-algorithm helpers about the last element
   and about sorted lists.  They are not laws of the monad/free-monoid
   structure and have no dedicated nLab or Wikipedia page; they support
   order-theoretic reasoning over lists elsewhere in the library.

--------
nLab: https://ncatlab.org/nlab/show/list+monad
nLab: https://ncatlab.org/nlab/show/free+monoid
Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

此文件收集关于列表类型的引理，其函子（functor）、应用函子（applicative）和单子（monad）实例位于父模块 [Theory.Coq.List] 中。该列表类型是自由幺半群（free monoid）在 A 上的基础集合，[app] 作为幺半群乘法，[[]] 作为其单位；下面的 [Forall_append] 引理表明谓词 [Forall P] 遵循该乘法。

此范围内的其余引理（[olast_*]、[Forall_ordered]、[StronglySorted_*]）是关于最后一个元素和排序列表的纯列表算法辅助工具。它们不是单子/自由幺半群结构的定律，也没有专门的 nLab 或 Wikipedia 页面；它们支持库中其他地方对列表的序理论推理。
*)

(*
Lemma foldl_cons : forall a (x : a) xs,
  foldl (fun us : list a => cons^~ us) [x] xs
    = foldl (fun us : list a => cons^~ us) [] [x & xs].
Proof. by move=> a x; elim. Qed.

Lemma rcons_nil : forall a us (u : a), rcons us u = [] → False.
Proof. by move=> a us u; case: us => // [|? ?] in u *. Qed.

--------
引理 foldl_cons : 对于所有 a (x : a) xs,
  foldl (fun us : list a => cons^~ us) [x] xs
    = foldl (fun us : list a => cons^~ us) [] [x & xs].
证明. 通过 move=> a x; 消除. 证毕.

引理 rcons_nil : 对于所有 a us (u : a), rcons us u = [] → 假.
证明. 通过 move=> a us u; case: us => // [|? ?] 在 u *. 证毕.
*)

Lemma olast_last : forall a (u : a) us,
  olast (u :: us) = Just (last us u).
Proof.
  intros a u.
  induction us as [|x xs IHxs]; simpl; trivial.
  generalize dependent u.
  destruct xs as [|y ys]; intros.
  - reflexivity.
  - exact IHxs.
Qed.

Lemma olast_spec : forall a (u : a) us, olast (u :: us) = Nothing → False.
Proof.
  intros a u.
  induction us as [|x xs IHxs]; simpl; intros.
  - discriminate.
  - rewrite olast_last in H.
    rewrite olast_last in IHxs.
    destruct xs as [|y ys]; discriminate.
Qed.

(*
Lemma olast_rcons : forall a (u : a) us, olast (rcons us u) = Just u.
Proof.
  move=> a u.
  elim=> //= [x xs IHxs].
  case: xs => // [|y ys] in IHxs *.
Qed.

--------
Lemma olast_rcons : 对于所有的 a (u : a) us，有 olast (rcons us u) = Just u。
证明。
  move=> a u。
  elim=> //= [x xs IHxs]。
  case: xs => // [|y ys] 在 IHxs *。
Qed.
*)

Lemma olast_cons : forall a (x y : a) ys,
  olast (x :: y :: ys) = olast (y :: ys).
Proof.
  intros a x y.
  induction ys as [|? xs IHxs]; trivial.
Qed.

(*
Lemma olast_cons_rcons : forall a (z u : a) us,
  olast (z :: rcons us u) = Just u.
Proof.
  move=> a z u.
  elim=> //= [x xs IHxs].
  case: xs => // [|y ys] in IHxs *.
Qed.

Lemma olast_cat : forall a (x : a) xs ys,
  olast (ys ++ x :: xs) = olast (x :: xs).
Proof.
  intros a y xs ys.
  induction xs as [|z zs IHzs].
    rewrite cats1, olast_rcons.
  replace [y, z & zs] with ([y] ++ [z & zs]).
    rewrite catA !IHzs.
  reflexivity.
Qed.

--------
引理 olast_cons_rcons : 对于所有 a (z u : a) us,
  olast (z :: rcons us u) = Just u。
证明。
  move=> a z u。
  消去=> //= [x xs IHxs]。
  情况分析: xs => // [|y ys] 在 IHxs * 中。
Qed.

引理 olast_cat : 对于所有 a (x : a) xs ys,
  olast (ys ++ x :: xs) = olast (x :: xs)。
证明。
  引入 a y xs ys。
  对 xs 使用归纳法作为 [|z zs IHzs]。
    重写 cats1, olast_rcons。
  将 [y, z & zs] 替换为 ([y] ++ [z & zs])。
    重写 catA !IHzs。
  自反性。
Qed。
*)

(*
Lemma olast_cat_rcons : forall a (x : a) xs ys,
  olast (ys ++ rcons xs x) = Just x.
Proof.
  move=> a y xs ys.
  elim: xs => /= [|z zs IHzs] in y ys *.
    by rewrite cats1 olast_rcons.
  rewrite olast_cat -cat1s.
  exact: IHzs.
Qed.

Lemma oends_spec a (l : list a) :
  match oends l with
  | Just (inr (x, y)) => head x l = x /\ last y l = y
  | Just (inl x)      => head x l = last x l
  | Nothing              => True
  end.
Proof.
  rewrite /oends.
  case: l => // [x xs].
  case/lastP: xs => //= [ys y].
  by rewrite last_rcons.
Qed.

Lemma last_leq : forall (z y : nat) (xs : list nat) (n : nat),
  last z xs <= n → y <= z → last y xs <= n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_trans IHxs _.
Qed.

Lemma last_leq_ltn : forall (z y : nat) (xs : list nat) (n : nat),
  last z xs < n → y <= z → last y xs < n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_ltn_trans IHxs _.
Qed.

Lemma last_ltn : forall (z y : nat) (xs : list nat) (n : nat),
  last z xs < n → y <= z → last y xs < n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_ltn_trans IHxs _.
Qed.

Lemma list_cons_nonzero : forall {a x} {xs l : list a},
  l = x :: xs → size l > 0.
Proof. by move=> a x xs l ->. Qed.

Lemma Forall_head : forall A P (x : A) xs,
  List.Forall P (x :: xs) → P (head x xs).
Proof.
  move=> A P x.
  elim=> /= [|y ys IHys] H.
    by inv H.
  by inv H; inv H3.
Qed.

Lemma Forall_rcons_inv : forall a P (x : a) xs,
  List.Forall P (rcons xs x) → List.Forall P xs /\ P x.
Proof.
  move=> a P x.
  elim=> [|y ys IHys] /=.
    by invert.
  invert.
  specialize (IHys H2).
  inversion IHys.
  split=> //.
  constructor=> //.
Qed.

Lemma Forall_last : forall A P (x : A) xs,
  List.Forall P (x :: xs) → P (last x xs).
Proof.
  move=> A P x.
  elim/last_ind=> /= [|ys y IHys] H.
    by inv H.
  inv H.
  rewrite last_rcons.
  apply Forall_rcons_inv in H3.
  by inv H3.
Qed.

--------
Lemma olast_cat_rcons ：对于所有 a (x : a) xs ys，
  olast (ys ++ rcons xs x) = Just x。
证明。
  move=> a y xs ys.
  elim: xs => /= [|z zs IHzs] 在 y ys * 中。
    by 重写 cats1 olast_rcons。
  重写 olast_cat -cat1s。
  精确：IHzs。
Qed.

引理 oends_spec a（l ： 列表 a）：
  将 oends 与 匹配
  |仅 （inr （x， y）） = >头 x l = x / \ 最后 y = y = y = y
  |仅 （inl x） = > 头 x l = 最后 x l
  |无 => 真
  结束。
证据。
  重写/oends。
  格：l => // [x xs]。
  case/lastP： xs = > //= [ys y]。
  通过重写last_rcons。
Qed。

引理 last_leq : 对于所有 (z y : 自然数) (xs : 自然数列表) (n : 自然数)，
  如果 last z xs <= n 且 y <= z，则 last y xs <= n。
证明。
  移动=> z y。
  归纳=> //= [x xs IHxs]。
  精确：leq_trans IHxs _。
证毕。

引理 last_leq_ltn : 对于所有 (z y : nat) (xs : list nat) (n : nat)，
  如果 last z xs < n 且 y <= z，则 last y xs < n。
证明。
  移动=> z y。
  消去=> //= [x xs IHxs]。
  精确: leq_ltn_trans IHxs _。
证毕。

引理 last_ltn : 对于任意 (z y : nat) (xs : list nat) (n : nat)，有
  last z xs < n → y <= z → last y xs < n。
证明。
  move=> z y。
  消去=> //= [x xs IHxs]。
  完全：leq_ltn_trans IHxs _。
Qed。

引理 list_cons_nonzero : 对于所有 {a x} {xs l : list a},
  如果 l = x :: xs 则 size l > 0.
证明. 通过 move=> a x xs l -> 完成. Qed.

Lemma Forall_head : 对于所有 A P (x : A) xs,
  如果 List.Forall P (x :: xs) → P (head x xs).
证明。
  move=> A P x.
  elim=> /= [|y ys IHys] H.
    通过 inv H.
  通过 inv H; inv H3.
Qed.

引理Forall_rcons_inv：对所有 P （x ： a） xs，
  列表。Forall P（rcons xs x） → 列表.forall P xs /\ P x.
证据。
  move=> a P x。
  elim=> [|y ys IHys] /=。
    由Invert制作。
  倒挂。
  专精（IHys H2）。
  反转的伊斯兰。
  split=> //。
  构造者=> //。
Qed。

引理 Forall_last : 对于所有 A P (x : A) xs,
  List.Forall P (x :: xs) → P (last x xs).
证明。
  move=> A P x.
  elim/last_ind=> /= [|ys y IHys] H.
    by inv H.
  inv H.
  rewrite last_rcons.
  apply Forall_rcons_inv in H3.
  by inv H3.
Qed.
*)

Lemma Forall_append : forall A (P : A → Prop) xs ys,
   List.Forall P xs /\ List.Forall P ys <-> List.Forall P (xs ++ ys).
Proof.
  intros A P xs ys.
  rewrite List.Forall_app.
  tauto.
Qed.

Lemma StronglySorted_inv_app : forall a R (l1 l2 : list a),
  StronglySorted R (l1 ++ l2)
    → StronglySorted R l1 /\ StronglySorted R l2.
Proof.
  intros a R l1 l2 H.
  induction l1 as [|x xs IHxs]; simpl in *.
  - split; [constructor|assumption].
  - inversion H; subst.
    specialize (IHxs H2).
    destruct IHxs as [Hs1 Hs2].
    split; [|assumption].
    constructor; [assumption|].
    apply List.Forall_app in H3.
    destruct H3 as [HF _].
    assumption.
Qed.

Lemma Forall_ordered : forall a (R : a → a → Prop) `{Transitive _ R} x y xs,
  R x y → List.Forall (R y) xs → List.Forall (R x) xs.
Proof.
  intros a R Htrans x y xs Hxy Hf.
  induction xs as [|z zs IHzs].
  - constructor.
  - inversion Hf; subst.
    constructor.
    + apply (Htrans x y z); assumption.
    + apply IHzs; assumption.
Qed.

Lemma StronglySorted_cat {A : Type} {xs ys : list A} {R : A → A → Prop}
  `{Transitive _ R} :
  StronglySorted R xs → StronglySorted R ys
    → (match olast xs, ys with
        | Just x, y :: _ => R x y
        | _, _ => True
        end)
    → StronglySorted R (xs ++ ys)%list.
Proof.
  intros Hsxs Hsys Hbridge.
  generalize dependent ys.
  induction Hsxs as [|x xs' Hsxs' IHxs Hfx]; intros ys Hsys Hbridge.
  - simpl. assumption.
  - simpl.
    (* Bridge derivation: for any y at head of ys, we need R x y / 桥推导：对于 ys 头部的任意 y，我们需要 R x y *)
    assert (Hxy_for_head : forall y ys', ys = y :: ys' → R x y).
    { intros y ys' Heq; subst ys.
      destruct xs' as [|x' xs''].
      - simpl in Hbridge. assumption.
      - rewrite olast_last in Hbridge.
        (* Hbridge : R (last xs'' x') y / H桥：R（最后 xs'' x'）y *)
        (* We need R x y. We have Forall (R x) (x' :: xs'') so R x (last xs'' x'), then transitivity. / 我们需要 R x y。我们有 Forall (R x) (x' :: xs'') 所以 R x (last xs'' x')，然后使用传递性。 *)
        assert (Hlast : forall (us : list A) (u : A),
                          List.Forall (R x) (u :: us) → R x (last us u)).
        { clear.
          intros us. induction us as [|z zs IH]; intros u Hf.
          - simpl. inversion Hf; subst. assumption.
          - destruct zs as [|w ws].
            + simpl. inversion Hf; subst. inversion H2; subst. assumption.
            + simpl. apply IH.
              inversion Hf; subst.
              inversion H2; subst.
              constructor; assumption.
        }
        specialize (Hlast xs'' x' Hfx).
        (*
Hlast : R x (last xs'' x'); Hbridge : R (last (x' :: xs'') x) y. / Hlast：R x（last xs'' x'）；Hbridge：R（last（x' :: xs''）x）y。

--------
Hlast：R x（last xs'' x'）；Hbridge：R（last（x' :: xs''）x）y。
*)
        (* Bridge the two forms: last (x' :: xs'') x = last xs'' x'. / 桥接这两种形式：last (x' :: xs'') x = last xs'' x'. *)
        assert (Heq : last (x' :: xs'') x = last xs'' x').
        { clear. destruct xs'' as [|z zs]; [reflexivity|].
          simpl. revert z. induction zs as [|w ws IH]; intros z.
          - reflexivity.
          - simpl. apply IH. }
        rewrite Heq in Hbridge.
        eapply transitivity; eassumption.
    }
    (* Now derive Forall (R x) ys / 现在推导 Forall (R x) ys *)
    assert (Hfys : List.Forall (R x) ys).
    { destruct ys as [|y ys'].
      - constructor.
      - assert (Hxy : R x y) by (apply (Hxy_for_head y ys'); reflexivity).
        constructor; [assumption|].
        inversion Hsys as [|? ? ? Hfy]; subst.
        eapply Forall_ordered; eassumption.
    }
    (* Apply IH / 应用 IH *)
    constructor.
    + apply IHxs; [assumption|].
      destruct xs' as [|x' xs''].
      * simpl. trivial.
      * (* olast (x' :: xs'') need to relate to ys. Use Hbridge which gives R (last xs'' x') y. / olast (x' :: xs'') 需要与 ys 相关。使用 Hbridge，它提供 R (last xs'' x') y。 *)
        destruct ys as [|y ys'].
        -- destruct (olast (x' :: xs'')); trivial.
        -- rewrite olast_last.
           rewrite olast_last in Hbridge.
           (* Same default-equivalence trick as in the bridge derivation / 与桥推导中相同的默认等价技巧 *)
           assert (Heq2 : last (x' :: xs'') x = last xs'' x').
           { clear. destruct xs'' as [|z zs]; [reflexivity|].
             simpl. revert z. induction zs as [|w ws IH]; intros z.
             - reflexivity.
             - simpl. apply IH. }
           rewrite Heq2 in Hbridge.
           assumption.
    + apply List.Forall_app.
      split; assumption.
Qed.

(*
Lemma StronglySorted_cat_cons
  {A : Type} {x y : A} {xs ys : list A} {R : A → A → Prop} `{Transitive _ R} :
  StronglySorted R (x :: xs) → StronglySorted R (y :: ys)
    → R (last x xs) y
    → StronglySorted R (x :: xs ++ y :: ys).
Proof.
  move=> Hsort1 Hsort2 Hrel.
  case/lastP: xs => /= [|xs1 x1] in Hsort1 Hrel *.
    constructor=> //.
    constructor=> //.
    inv Hsort2.
    have: forall a : A, R y a → R x a.
      move=> a Ha.
      exact: transitivity Hrel Ha.
    move/List.Forall_impl.
    exact.
  rewrite -cat_cons.
  apply: StronglySorted_cat => //.
  rewrite olast_cons_rcons.
  by rewrite last_rcons in Hrel.
Qed.

--------
Lemma StronglySorted_cat_cons
  {A : 类型} {x y : A} {xs ys : 列表 A} {R : A → A → 命题} `{传递性 _ R} :
  StronglySorted R (x :: xs) → StronglySorted R (y :: ys)
    → R (last x xs) y
    → StronglySorted R (x :: xs ++ y :: ys).
证明.
  move=> Hsort1 Hsort2 Hrel.
  case/lastP: xs => /= [|xs1 x1] 在 Hsort1 Hrel *.
    构造器=> //.
    构造器=> //.
    反转 Hsort2.
    有: 对于所有 a : A, 如果 R y a 则 R x a.
      move=> a Ha.
      精确: 传递性 Hrel Ha.
    move/List.Forall_impl.
    精确.
  重写 -cat_cons.
  应用: StronglySorted_cat => //.
  重写 olast_cons_rcons.
  通过重写 last_rcons 在 Hrel 中.
证明结束.
*)

Lemma StronglySorted_cons_cons : forall a (R : a → a → Prop) x xs y ys,
  StronglySorted R (x :: xs ++ y :: ys) → R x y.
Proof.
  intros a R x xs y ys H.
  inversion H; subst.
  apply List.Forall_app in H3.
  destruct H3 as [_ HF].
  inversion HF; subst.
  assumption.
Qed.

(*
Lemma StronglySorted_rcons_inv : forall a R (x : a) xs,
  StronglySorted R (rcons xs x) → StronglySorted R xs.
Proof.
  move=> a R x.
  elim=> [|y ys IHys] /=.
    by invert.
  invert.
  specialize (IHys H1).
  constructor=> //.
  apply Forall_rcons_inv in H2.
  by inversion H2.
Qed.

Lemma Forall_rcons_rcons : forall a R `{Transitive _ R} (x : a) y z xs,
  List.Forall (R z) (rcons xs x) → R x y
    → List.Forall (R z) (rcons (rcons xs x) y).
Proof.
  move=> a R H x y z.
  elim=> [|w ws IHws] /=.
    constructor.
      by inv H0.
    constructor.
      inv H0.
      exact: transitivity H4 H1.
    by constructor.
  constructor.
    by inv H0.
  apply: IHws => //.
  by inv H0.
Qed.

--------
Lemma StronglySorted_rcons_inv : 对于所有 a R (x : a) xs,
  StronglySorted R (rcons xs x) → StronglySorted R xs.
证明。
  move=> a R x.
  归纳=> [|y ys IHys] /=.
    通过反转完成。
  反转。
  特化 (IHys H1)。
  构造=> //。
  应用 Forall_rcons_inv 在 H2。
  通过反演 H2 完成。
证毕。

Lemma Forall_rcons_rcons : 对于所有 a R `{Transitive _ R} (x : a) y z xs,
  List.Forall (R z) (rcons xs x) → R x y
    → List.Forall (R z) (rcons (rcons xs x) y).
证明。
  move=> a R H x y z.
  归纳=> [|w ws IHws] /=.
    构造。
      通过反演 H0 完成。
    构造。
      反演 H0。
      精确地应用：transitivity H4 H1。
    通过构造完成。
  构造。
    通过反演 H0 完成。
  应用：IHws => //。
  通过反演 H0 完成。
证毕。
*)

(*
Forall_ordered: moved earlier in the file (to its definition site above)
   because it is consumed by StronglySorted_cat.  This note marks its former
   location; the lemmas that follow remain commented out for continuity.

--------
Forall_ordered：在文件中提前移动（到其定义位置上方），因为它被 StronglySorted_cat 使用。此备注标记了其以前的位置；随后的引理仍然被注释以保持连续性。
*)

(*
Lemma StronglySorted_rcons_rcons : forall a R `{Transitive _ R} (x : a) y xs,
  StronglySorted R (rcons xs x) → R x y
    → StronglySorted R (rcons (rcons xs x) y).
Proof.
  move=> a R H x y.
  elim=> [|z zs IHzs] /=.
    by repeat constructor.
  constructor.
    inv H0.
   exact: (IHzs H4).
 inv H0.
 exact: Forall_rcons_rcons.
Qed.

Lemma StronglySorted_rcons_rcons_inv : forall a R (x y : a) xs,
  StronglySorted R (rcons (rcons xs x) y) → R x y.
Proof.
  move=> a R x y.
  elim=> [|z zs IHzs] /=.
    invert.
    by inv H2.
  invert.
  exact: IHzs H1.
Qed.

Example ex_foldl_with_index_1 :
  foldl_with_index (fun n z x => (n, x) :: z) nil [1; 2; 3]
  eq_dec   [(2, 3); (1, 2); (0, 1)].
Proof. reflexivity. Qed.

Example ex_foldr_with_index_1 :
  foldr_with_index (fun n x z => (n, x) :: z) nil [1; 2; 3]
  eq_dec   [(0, 1); (1, 2); (2, 3)].
Proof. reflexivity. Qed.

Lemma span_cat {a} (l : list a) : forall p l1 l2,
  (l1, l2) = span p l
    → l = l1 ++ l2 /\ all p l1 /\ (if l2 is x :: _ then ~~ (p x) else True).
Proof.
  move=> p.
  elim: l => /= [|x xs IHxs] l1 l2 Heqe.
    by inv Heqe.
  case E: (p x); rewrite E in Heqe.
    case S: (span p xs) => [l l0] in IHxs Heqe *.
    inv Heqe.
    move: (IHxs l l0 (refl_equal _)) => [? [? ?]].
    split; first by congr (_ :: _).
    split=> //.
    by apply/andP; split=> //.
  inv Heqe.
  split=> //.
  split=> //.
  by apply/negbT.
Qed.

Example span_ex1 :
  span (fun x => x < 10) [1; 5; 10; 15] = ([1; 5], [10; 15]).
Proof. reflexivity. Qed.

Example groupBy_ex1 :
  groupBy eq_op [1; 3; 3; 4; 5; 5; 9; 6; 8]
    = [[1]; [3; 3]; [4]; [5; 5]; [9]; [6]; [8]].
Proof. reflexivity. Qed.

Lemma partition_all {a} {p q : a → bool} (xs : list a) :
  all p xs → let: (ys, zs) := partition q xs in
              all (fun x => p x && q x) ys &&
              all (fun x => p x && ~~ q x) zs.
Proof.
  move=> H.
  elim: xs => //= [x xs IHxs] in H *.
  case: (partition q xs) => [ys zs] /= in IHxs *.
  move/andP: H => [H1 H2].
  specialize (IHxs H2).
  case E: (q x) => /=.
    by ordered.
  move/negbT in E.
  by ordered.
Qed.

Lemma perm_eq_nil : forall (a : eqType) (xs : list a),
  perm_eq [] xs → xs = [].
Proof.
  move=> a.
  elim=> //= [x xs IHxs].
  rewrite /perm_eq /=.
  move/andP => [H1 H2].
  rewrite eq_refl /= in H1.
  discriminate H1.
Qed.

Lemma all_perm : forall (a : eqType) (xs ys : list a),
  perm_eq xs ys → all^~ xs =1 all^~ ys.
Proof.
  move=> a xs ys H P.
  move/perm_eq_mem in H.
  by rewrite (eq_all_r H).
Qed.

Lemma all_catC {a} (P : pred a) (xs ys : list a) :
  all P (xs ++ ys) = all P (ys ++ xs).
Proof.
  case: xs => /= [|x xs] in ys *.
    by rewrite cats0.
  case: ys => // [|y ys].
    by rewrite cats0.
  by rewrite !all_cat /= andbA andbC.
Qed.

Lemma all_flip : forall A (P : rel A) (_ : symmetric P) x (xs : list A),
  all (P x) xs = all (P ^~ x) xs.
Proof.
  move=> A P H x.
  elim=> //= [y ys IHys].
  by rewrite -IHys H.
Qed.

Lemma all_all_cons : forall a (xs ys : list a) (x : a) (R : rel a),
  all (fun y : a => all (R y) (x :: xs)) ys =
  all (R ^~ x) ys && all (fun y : a => all (R y) xs) ys.
Proof.
  move=> a xs ys x R.
  elim: ys => // [y ys IHys].
  rewrite [all]lock -{1}lock /= -lock IHys /= -!andbA.
  congr (_ && _).
  by rewrite and_swap.
Qed.

Lemma all_all_cat : forall A (P : rel A) (xs ys zs : list A),
  all (fun x => all (P x) (xs ++ ys)) zs
    = all (fun x => all (P x) xs) zs && all (fun x => all (P x) ys) zs.
Proof.
  move=> A P xs ys.
  elim=> //= [z zs IHzs].
  rewrite IHzs all_cat.
  rewrite !andbA.
  congr (_ && _).
  rewrite -!andbA.
  congr (_ && _).
  by rewrite andbC.
Qed.

Lemma all_all_flip : forall A (P : rel A) (_ : symmetric P) (xs ys : list A),
  all (fun x => all (P x) ys) xs = all (fun x => all (P ^~ x) ys) xs.
Proof.
  move=> A P H.
  elim=> //= [z zs IHzs] ys.
  by rewrite -IHzs all_flip.
Qed.

Lemma perm_cat_cons (T : eqType) (x : T) : forall (s1 s2 : list_predType T),
  perm_eql (x :: s1 ++ s2) (s1 ++ x :: s2).
Proof.
  move=> s1 s2.
  apply/perm_eqlP.
  rewrite perm_eq_sym perm_catC cat_cons perm_cons perm_catC.
  exact: perm_eq_refl.
Qed.

Lemma perm_rem_cons (T : eqType) (x : T) : forall (s1 s2 : list_predType T),
  x \in s1 → perm_eql (rem x s1 ++ x :: s2) (s1 ++ s2).
Proof.
  move=> s1 s2 Hin.
  apply/perm_eqlP.
  rewrite perm_catC cat_cons perm_cat_cons perm_catC perm_cat2r perm_eq_sym.
  exact: perm_to_rem.
Qed.

Lemma has_size : forall (a : eqType) x (xs : list a), x \in xs → 0 < size xs.
Proof. move=> a x; elim=> //. Qed.

Example sortBy_ex1 :
  sortBy ltn [1; 3; 5; 7; 9; 2; 4; 6; 8] = [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. reflexivity. Qed.

Example sortBy_ex2 :
  sortBy gtn [1; 3; 5; 7; 9; 2; 4; 6; 8] = [9; 8; 7; 6; 5; 4; 3; 2; 1].
Proof. reflexivity. Qed.

Example sortBy_ex3 :
  sortBy (fun x y => false) [1; 3; 5; 7; 9; 2; 4; 6; 8] =
                            [1; 3; 5; 7; 9; 2; 4; 6; 8].
Proof. reflexivity. Qed.

Lemma Forall_insert : forall a (R : a → a → bool) `{Transitive _ R} x xs y,
  R x y → List.Forall (R x) xs → List.Forall (R x) (insert R y xs).
Proof.
  move=> a R H x xs y H1 H2.
  elim: xs => [|z zs IHzs] /= in H1 H2 *.
    rewrite /insert.
    by constructor.
  rewrite /insert /= -/insert.
  case E: (R z y).
    constructor.
      by inv H2.
    apply: IHzs => //.
    by inv H2.
  constructor=> //.
Qed.

Lemma StronglySorted_insert :
  forall a (R : a → a → bool) `{Transitive _ R} x xs,
  StronglySorted R xs → (forall y, ~~ R y x → R x y)
    → StronglySorted R (insert R x xs).
Proof.
  move=> a R H x xs H1 H2.
  elim=> [|y ys IHys] /= in H1 *.
    rewrite /insert.
    by constructor; constructor.
  rewrite /insert /= -/insert.
  case E: (R y x).
    constructor=> //.
    exact: Forall_insert.
  constructor.
    constructor=> //.
    constructor.
    apply/H2.
    by rewrite E.
  move/negbT/H2 in E.
  exact: (@Forall_ordered _ R H x y ys E H1).
Qed.

Lemma StronglySorted_impl_cons : forall a (R : a → a → bool) `{Transitive _ R}
  x y (ys : list a), StronglySorted R (x :: y :: ys) → R x (last y ys).
Proof.
  move=> a R H x y ys Hsort.
  elim: ys => [|z zs IHzs] /= in x y Hsort *.
    by inv Hsort; inv H3.
  apply: IHzs.
  inv Hsort; inv H2; inv H4.
  constructor=> //.
    constructor=> //.
  inv H3; inv H5.
  constructor=> //.
    by transitivity y.
  exact: (Forall_ordered H4).
Qed.

Lemma sortBy_sorted : forall a (R : a → a → bool) `{Transitive _ R} xs,
  (forall x y, ~~ R y x → R x y) → StronglySorted R (sortBy R xs).
Proof.
  move=> a R H xs H1.
  elim: xs => [|x xs IHxs] /=.
    by constructor.
  apply: StronglySorted_insert => //.
  exact: (H1 x).
Qed.

Lemma insert_all : forall a (P : a → bool) (R : a → a → bool) x xs,
  all P (insert R x xs) = P x && all P xs.
Proof.
  move=> a P R x.
  elim=> //= [u us IHus].
  rewrite /insert /= -/insert.
  case: (R u x) => //=.
  by rewrite IHus and_swap.
Qed.

Lemma sortBy_all : forall a (P : a → bool) (R : a → a → bool) xs,
  all P xs = all P (sortBy R xs).
Proof.
  move=> a P R.
  elim=> //= [u us IHus].
  by rewrite IHus insert_all.
Qed.

Lemma perm_cons_swap (T : eqType) (x y : T) : forall (xs : list_predType T),
  perm_eql (x :: y :: xs) (y :: x :: xs).
Proof.
  move=> xs; apply/perm_eqlP.
  rewrite -cat1s perm_catC cat_cons perm_cons perm_catC cat1s.
  exact: perm_eq_refl.
Qed.

Lemma insert_perm (T : eqType) P (x : T) : forall (xs : list_predType T),
  perm_eql (insert P x xs) (x :: xs).
Proof.
  elim=> //= [y ys IHys]; rewrite /insert.
  case: (P y x) => //=; apply/perm_eqlP.
  rewrite perm_eq_sym perm_cons_swap perm_cons perm_eq_sym -/insert.
  exact/perm_eqlP/IHys.
Qed.

Lemma insert_size : forall a P (x : a) xs,
  size (insert P x xs) = (size xs).+1.
Proof.
  move=> a P x xs.
  elim: xs => //= [y ys IHys].
  rewrite /insert /= -/insert.
  case: (P y x) => //=.
  by rewrite IHys.
Qed.

Lemma proj_rem_uniq (a b : eqType) (f : a → b) : forall x xs,
  uniq [list f i | i <- xs] → uniq [list f i | i <- rem x xs].
Proof. by move=> x xs; apply/sublist_uniq/map_sublist/rem_sublist. Qed.

Lemma in_proj : forall (a b : eqType) (x : a) (y : b) (xs : list (a * b)),
  (x \notin [list fst i | i <- xs]) ||
  (y \notin [list snd i | i <- xs]) → (x, y) \notin xs.
Proof.
  move=> a b x y.
  elim=> //= [z zs IHzs] H1.
  move/orP: H1 => [H1|H1];
  rewrite in_cons;
  rewrite in_cons in H1;
  apply/norP;
  move/norP: H1 => [H2 H3];
  (split;
   [ case: z => /= [j k] in H2 *;
     move/eqP in H2;
     apply/eqP;
     move=> Hneg;
     inversion Hneg;
     contradiction
   | apply: IHzs;
     apply/orP ]).
    by left.
  by right.
Qed.

Lemma uniq_proj : forall (a b : eqType) (xs : list (a * b)),
  uniq [list fst i | i <- xs] ->
  uniq [list snd i | i <- xs] → uniq xs.
Proof.
  move=> a b.
  elim=> //= [x xs IHxs] /andP [H1 H2] /andP [H3 H4].
  case: x => /= [j k] in H1 H3 *.
  apply/andP; split; last exact: IHxs.
  apply: in_proj.
  apply/orP; by left.
Qed.

Lemma sublist_in_cons : forall (a : eqType) x y (xs ys : list a),
  sublist (x :: xs) (y :: ys) → x != y → sublist (x :: xs) ys.
Proof.
  move=> a x y xs ys Hsub Hneq.
  elim: ys => /= [|z zs IHzs] in Hsub *.
    case E: (eq_dec x y).
      move/negP: Hneq.
      by rewrite E.
    rewrite E in Hsub.
    inversion Hsub.
  case E: (eq_dec x y).
    move/negP: Hneq.
    by rewrite E.
  rewrite E in Hsub.
  assumption.
Qed.

Lemma sublist_sing : forall (a : eqType) (x : a) xs s,
  sublist (x :: xs) s → sublist [x] s.
Proof.
  move=> a x xs s Hsub.
  elim: s => // [y ys IHys] in Hsub *.
  rewrite sub1list.
  rewrite sub1list in IHys.
  rewrite in_cons.
  apply/orP.
  case E: (eq_dec x y).
    by left.
  right.
  move/negP in E.
  move/negP in E.
  apply: IHys.
  apply: sublist_in_cons.
    exact Hsub.
  exact E.
Qed.

Lemma in_sublist_sing : forall {E : eqType} (s : list E) v (y : E) ys,
  v = y :: ys → sublist v s → y \in s.
Proof.
  move=> E s v y ys ->.
  rewrite -sub1list.
  exact: sublist_sing.
Qed.

Lemma sublist_cons_add : forall (a : eqType) (x : a) xs s,
  sublist xs s → sublist xs (x :: s).
Proof.
  move=> a x.
  elim=> // [y ys IHys] s Hsub.
  rewrite /=.
  case: (eq_dec y x).
    apply: sublist_impl_cons.
    exact Hsub.
  exact.
Qed.

Lemma sublist_cons_rem : forall (a : eqType) (x : a) xs s,
  sublist (x :: xs) s → sublist xs (rem x s).
Proof.
  move=> a x xs.
  elim=> //= [y ys IHys].
  rewrite eq_sym.
  case E: (eq_dec y x); first exact.
  move/IHys => Hsub {IHys}.
  exact: sublist_cons_add.
Qed.

Lemma all_xpredT_true : forall a (xs : list a), all xpredT xs.
Proof. by move=> ?; elim. Qed.

Lemma between_all_cat : forall a (xs ys : list a) (R : rel a),
  between_all R (xs ++ ys) =
  [&& between_all R xs
  ,   between_all R ys
  ,   all (fun x => all (R x) ys) xs
  &   all (fun y => all (R ^~ y) xs) ys
  ].
Proof.
  move=> a xs ys R.
  elim: xs => [|x xs IHxs] in ys *.
    by rewrite /= all_xpredT_true Bool.andb_true_r.
  rewrite cat_cons all_all_cons.
  rewrite /= all_cat {}IHxs /=.
  rewrite !andbA; f_equal.
  rewrite [X in _ = X]andbC.
  rewrite !andbA; f_equal.
  rewrite [X in _ = X]andbC.
  rewrite !andbA; f_equal.
  rewrite Bool.andb_diag.
  by rewrite -!andbA and_swap.
Qed.

Lemma between_all_catC {a} (xs ys : list a) (R : rel a) (_ : symmetric R) :
  between_all R (xs ++ ys) = between_all R (ys ++ xs).
Proof.
  elim: xs => /= [|x xs IHxs] in ys *.
    by rewrite cats0.
  rewrite IHxs.
  elim: ys => /= [|y ys IHys].
    by rewrite cats0.
  rewrite -IHys !andbA.
  congr (_ && _).
  rewrite !all_cat -!andbA 2!andbA and_swap.
  congr (_ && _).
  rewrite andbC -!andbA [RHS]and_swap.
  congr (_ && _).
  rewrite [RHS]and_swap.
  congr (_ && _).
  by rewrite H.
Qed.

Lemma allpairs_map :
  forall a b c (f : a → b → c) (xs : list a) (ys : list b),
  [list f x y | x <- xs, y <- ys] =
  flatten [list [list f x y | y <- ys] | x <- xs].
Proof.
  move=> a b c f.
  elim=> //= [x xs IHxs] y.
  congr (_ ++ _).
  exact: IHxs.
Qed.

--------
引理 StronglySorted_rcons_rcons : 对于所有 a R ` {Transitive _ R} (x : a) y xs,
  如果 StronglySorted R (rcons xs x) 并且 R x y
  则 StronglySorted R (rcons (rcons xs x) y).
证明.
  move=> a R H x y.
  归纳法=> [|z zs IHzs] /=.
    使用 repeat constructor 完成.
  constructor.
    inv H0.
   精确: (IHzs H4).
 inv H0.
 精确: Forall_rcons_rcons.
Qed.

Lemma StronglySorted_rcons_rcons_inv : 对于所有 a R (x y : a) xs,
  StronglySorted R (rcons (rcons xs x) y) → R x y.
证明。
  move=> a R x y.
  elim=> [|z zs IHzs] /=.
    invert.
    by inv H2.
  invert.
  exact: IHzs H1.
Qed.

示例 ex_foldl_with_index_1 ：
  foldl_with_index (fun n z x => (n, x) :: z) nil [1; 2; 3]
  eq_dec   [(2, 3); (1, 2); (0, 1)]。
证明。 自反性。 证毕。

示例 ex_foldr_with_index_1 ：
  foldr_with_index (fun n x z => (n, x) :: z) nil [1; 2; 3]
  eq_dec   [(0, 1); (1, 2); (2, 3)]。
证明。 自反性。 证毕。

引理 span_cat {a} (l : list a) : 对于所有的 p l1 l2,
  (l1, l2) = span p l
    → l = l1 ++ l2 /\ all p l1 /\ (如果 l2 是 x :: _ 则 ~~ (p x) 否则 True).
证明。
  先移动=> p。
  对 l 使用归纳 => /= [|x xs IHxs] l1 l2 Heqe。
    通过 inv Heqe 完成。
  情况分析 E: (p x); 在 Heqe 中用 E 重写。
    情况分析 S: (span p xs) => [l l0] 在 IHxs Heqe *。
    inv Heqe。
    移动: (IHxs l l0 (refl_equal _)) => [? [? ?]。
    分割; 首先通过 congr (_ :: _) 完成。
    分割=> //。
    通过 apply/andP; 分割完成//。
  inv Heqe。
  分割=> //。
  分割=> //。
  通过 apply/negbT 完成。
Qed.

示例 span_ex1 ：
  span (fun x => x < 10) [1; 5; 10; 15] = ([1; 5], [10; 15]).
证明。 自反性。 证毕。

示例 groupBy_ex1 ：
  groupBy eq_op [1; 3; 3; 4; 5; 5; 9; 6; 8]
    = [[1]; [3; 3]; [4]; [5; 5]; [9]; [6]; [8]].
证明。自反性。证毕。

引理 partition_all {a} {p q : a → bool} (xs : list a) :
  all p xs → 设 (ys, zs) := partition q xs in
              all (fun x => p x && q x) ys &&
              all (fun x => p x && ~~ q x) zs.
证明.
  move=> H.
  归纳: xs => //= [x xs IHxs] 在 H * 中.
  情况分析: (partition q xs) => [ys zs] /= 在 IHxs * 中.
  move/andP: H => [H1 H2].
  特例化 (IHxs H2).
  情况 E: (q x) => /=.
    通过 ordered.
  move/negbT 在 E 中.
  通过 ordered.
Qed.

引理 perm_eq_nil : 对于所有 (a : eqType) (xs : list a)，
  perm_eq [] xs → xs = []。
证明。
  move=> a。
  elim=> //= [x xs IHxs]。
  rewrite /perm_eq /=。
  move/andP => [H1 H2]。
  rewrite eq_refl /= 在 H1 中。
  discriminate H1。
Qed。

引理 all_perm : 对于所有 (a : eqType) (xs ys : list a)，若 perm_eq xs ys，则 all^~ xs =1 all^~ ys。
证明。
  move=> a xs ys H P。
  move/perm_eq_mem in H。
  通过重写 (eq_all_r H) 完成。
Qed.

引理 all_catC {a} (P : pred a) (xs ys : list a) ：
  all P (xs ++ ys) = all P (ys ++ xs).
证明。
  分情况: xs => /= [|x xs] 在 ys *。
    通过重写 cats0 完成。
  分情况: ys => // [|y ys]。
    通过重写 cats0 完成。
  通过重写 !all_cat /= andbA andbC 完成。
证毕。

引理 all_flip : 对于所有类型 A （P 是 A 上的关系）(_ : P 对称) x (xs : A 列表)，
  all (P x) xs = all (P ^~ x) xs。
证明。
  move=> A P H x。
  elim=> //= [y ys IHys]。
  by rewrite -IHys H。
Qed.

引理 all_all_cons : 对于所有 a (xs ys : 列表 a) (x : a) (R : 关系 a)，
  all (fun y : a => all (R y) (x :: xs)) ys =
  all (R ^~ x) ys && all (fun y : a => all (R y) xs) ys。
证明。
  move=> a xs ys x R。
  消元: ys => // [y ys IHys]。
  重写 [all]lock -{1}lock /= -lock IHys /= -!andbA。
  一致 (_ && _)。
  通过重写 and_swap 完成。
Qed。

引理 all_all_cat : 对所有 A (P : 关系 A) (xs ys zs : 列表 A)，有
  all (fun x => all (P x) (xs ++ ys)) zs
    = all (fun x => all (P x) xs) zs && all (fun x => all (P x) ys) zs。
证明。
  move=> A P xs ys。
  elim=> //= [z zs IHzs]。
  重写 IHzs all_cat。
  重写 !andbA。
  保持一致 (_ && _)。
  重写 -!andbA。
  保持一致 (_ && _)。
  by 重写 andbC。
Qed。

引理 all_all_flip : 对于所有 A (P : A 的关系) (_ : 对称的 P) (xs ys : A 的列表)，
  all (fun x => all (P x) ys) xs = all (fun x => all (P ^~ x) ys) xs。
证明。
  move=> A P H。
  elim=> //= [z zs IHzs] ys。
  通过重写 -IHzs all_flip 完成。
Qed。

引理 perm_cat_cons (T : eqType) (x : T) : 对于所有 (s1 s2 : list_predType T)，
  perm_eql (x :: s1 ++ s2) (s1 ++ x :: s2)。
证明。
  移动=> s1 s2。
  应用/perm_eqlP。
  重写 perm_eq_sym perm_catC cat_cons perm_cons perm_catC。
  精确：perm_eq_refl。
证毕。

引理 perm_rem_cons (T : eqType) (x : T) : 对于所有 (s1 s2 : list_predType T)，如果 x ∈ s1，则有 perm_eql (rem x s1 ++ x :: s2) (s1 ++ s2)。
证明。
  假设 => s1 s2 Hin。
  应用/perm_eqlP。
  重写 perm_catC cat_cons perm_cat_cons perm_catC perm_cat2r perm_eq_sym。
  精确应用: perm_to_rem。
证毕。

引理has_size ： forall （a ： eqType） x （xs ： list a）， x \in xs → 0 < 大小 xs。
证明。move=> a x;elim= > //。Qed。

示例 sortBy_ex1 ：
  sortBy ltn [1; 3; 5; 7; 9; 2; 4; 6; 8] = [1; 2; 3; 4; 5; 6; 7; 8; 9]。
证明。 自反性。 证明完毕。

示例 sortBy_ex2 ：
  sortBy gtn [1; 3; 5; 7; 9; 2; 4; 6; 8] = [9; 8; 7; 6; 5; 4; 3; 2; 1]。
证明。 自反性。 证毕。

示例 sortBy_ex3 ：
  sortBy (fun x y => false) [1; 3; 5; 7; 9; 2; 4; 6; 8] =
                            [1; 3; 5; 7; 9; 2; 4; 6; 8]。
证明。自反性。证毕。

引理 Forall_insert : 对于所有 a (R : a → a → bool) `{Transitive _ R} x xs y,
  如果 R x y 成立 且 List.Forall (R x) xs 成立，则 List.Forall (R x) (insert R y xs) 成立。
证明：
  move=> a R H x xs y H1 H2。
  用归纳法处理 xs => [|z zs IHzs] /= 在 H1 H2 * 中。
    重写 /insert。
    用构造子完成。
  重写 /insert /= -/insert。
  情况分析 E: (R z y)。
    构造子。
      通过 inv H2 完成。
    应用 IHzs => //。
    通过 inv H2 完成。
  构造子 => //。
Qed.

Lemma StronglySorted_insert ：
  对于所有 a (R : a → a → bool) `{Transitive _ R} x xs，
  若 StronglySorted R xs → （对所有 y，~~ R y x → R x y）
    则 StronglySorted R (insert R x xs)。
证明。
  move=> a R H x xs H1 H2。
  elim=> [|y ys IHys] /= 在 H1 * 中。
    重写 /insert。
    by 构造； 构造。
  重写 /insert /= -/insert。
  case E: (R y x)。
    构造=> //。
    精确: Forall_insert。
  构造。
    构造=> //。
    构造。
    应用 /H2。
    by 重写 E。
  移动 /negbT /H2 在 E 中。
  精确: (@Forall_ordered _ R H x y ys E H1)。
Qed.

Lemma StronglySorted_impl_cons : 对于所有 a (R : a → a → bool) `{Transitive _ R}
  x y (ys : list a), 如果 StronglySorted R (x :: y :: ys) 则 R x (last y ys).
证明。
  move=> a R H x y ys Hsort。
  用 ys 作归纳 => [|z zs IHzs] /= 在 x y Hsort * 中。
    通过反演 Hsort 并反演 H3 即可。
  应用: IHzs。
  反演 Hsort; 反演 H2; 反演 H4。
  构造=> //。
    构造=> //。
  反演 H3; 反演 H5。
  构造=> //。
    通过传递性 y 即可。
  精确: (Forall_ordered H4)。
Qed.

Lemma sortBy_sorted : 对于所有类型 a，及关系 R : a → a → bool，且 `{Transitive _ R} xs，
  (对于所有 x y，如果 ~~ R y x 则 R x y) → StronglySorted R (sortBy R xs)。
证明.
  move=> a R H xs H1。
  使用归纳法: xs => [|x xs IHxs] /=。
    直接由构造函数得出。
  应用: StronglySorted_insert => //。
  精确使用: (H1 x)。
Qed。

引理 insert_all：对于所有 a (P : a → bool) (R : a → a → bool) x xs，
  all P (insert R x xs) = P x && all P xs。
证明。
  move=> a P R x。
  elim=> //= [u us IHus]。
  rewrite /insert /= -/insert。
  case: (R u x) => //=。
  by rewrite IHus and_swap。
Qed.

Lemma sortBy_all : 对于所有 a (P : a → bool) (R : a → a → bool) xs,
  all P xs = all P (sortBy R xs).
证明。
  move=> a P R.
  elim=> //= [u us IHus].
  通过重写 IHus insert_all 完成。
Qed.

Lemma perm_cons_swap (T : eqType) (x y : T) : 对于所有 (xs : list_predType T)，有
  perm_eql (x :: y :: xs) (y :: x :: xs)。
证明。
  move=> xs; 应用/perm_eqlP。
  重写 -cat1s perm_catC cat_cons perm_cons perm_catC cat1s。
  精确: perm_eq_refl。
Qed。

引理 insert_perm (T : eqType) P (x : T) : 对于所有 (xs : list_predType T)，
  perm_eql (insert P x xs) (x :: xs)。
证明。
  elim=> //= [y ys IHys]; 重写 /insert。
  case: (P y x) => //=; 应用/perm_eqlP。
  重写 perm_eq_sym perm_cons_swap perm_cons perm_eq_sym -/insert。
  精确/perm_eqlP/IHys。
Qed。

引理 insert_size : 对于所有 a P (x : a) xs,
  size (insert P x xs) = (size xs).+1.
证明。
  move=> a P x xs.
  消去: xs => //= [y ys IHys].
  重写 /insert /= -/insert.
  情况分类: (P y x) => //=.
  通过重写 IHys 完成。
Qed.

引理 proj_rem_uniq (a b : eqType) (f : a → b) : 对于所有 x xs，
  uniq [list f i | i <- xs] → uniq [list f i | i <- rem x xs].
证明。通过 move=> x xs; 应用/sublist_uniq/map_sublist/rem_sublist. 证毕。

引理 in_proj : 对于所有 (a b : eqType) (x : a) (y : b) (xs : list (a * b))，
  (x 
otin [list fst i | i <- xs]) ||
  (y 
otin [list snd i | i <- xs]) → (x, y) 
otin xs.
证明。
  move=> a b x y.
  elim=> //= [z zs IHzs] H1.
  move/orP: H1 => [H1|H1];
  rewrite in_cons;
  rewrite in_cons in H1;
  apply/norP;
  move/norP: H1 => [H2 H3];
  (split;
   [ case: z => /= [j k] in H2 *;
     move/eqP in H2;
     apply/eqP;
     move=> Hneg;
     inversion Hneg;
     contradiction
   | apply: IHzs;
     apply/orP ]).
    by left.
  by right.
Qed.

引理 uniq_proj : 对于所有 (a b : eqType) (xs : list (a * b))，
  uniq [list fst i | i <- xs] ->
  uniq [list snd i | i <- xs] -> uniq xs.
证明。
  move=> a b.
  elim=> //= [x xs IHxs] /andP [H1 H2] /andP [H3 H4].
  case: x => /= [j k] 在 H1 H3 * 中。
  apply/andP; 分裂; 最后精确: IHxs.
  apply: in_proj.
  apply/orP; 通过左边完成.
Qed.

引理 sublist_in_cons : 对于所有 (a : eqType) x y (xs ys : list a)，
  sublist (x :: xs) (y :: ys) → x != y → sublist (x :: xs) ys.
证明。
  move=> a x y xs ys Hsub Hneq。
  elim: ys => /= [|z zs IHzs] 在 Hsub * 中。
    case E: (eq_dec x y)。
      move/negP: Hneq。
      通过重写 E。
    在 Hsub 中重写 E。
    对 Hsub 进行反演。
  case E: (eq_dec x y)。
    move/negP: Hneq。
    通过重写 E。
  在 Hsub 中重写 E。
  假设成立。
Qed.

引理 sublist_sing : 对于所有 (a : eqType) (x : a) xs s，
  如果 sublist (x :: xs) s，那么 sublist [x] s。
证明。
  移动=> a x xs s Hsub。
  对 s 进行归纳 => // [y ys IHys] 在 Hsub *中。
  重写 sub1list。
  在 IHys 中重写 sub1list。
  重写 in_cons。
  应用/orP。
  情况 E: (eq_dec x y)。
    通过左边完成。
  右边。
  移动/negP 到 E 中。
  移动/negP 到 E 中。
  应用: IHys。
  应用: sublist_in_cons。
    精确 Hsub。
  精确 E。
证毕。

引理 in_sublist_sing ： forall {E ： eqType} （s ： 列表 E） v （y ： E） ys，
  v = y ：： ys →子列表 v s 的 s / y \in s →
证据。
  move=> E s v y ys ->。
  重写 -sub1list。
  没错：sublist_sing。
Qed。

Lemma sublist_cons_add：对所有 (a : eqType) (x : a) xs s，
  如果 sublist xs s → sublist xs (x :: s)。
证明。
  move=> a x。
  elim=> // [y ys IHys] s Hsub。
  rewrite /=。
  case: (eq_dec y x)。
    apply: sublist_impl_cons。
    exact Hsub。
  exact。
Qed。

Lemma sublist_cons_rem : 对于所有 (a : eqType) (x : a) xs s,
  如果 sublist (x :: xs) s，那么 sublist xs (rem x s).
证明。
  move=> a x xs.
  归纳法=> //= [y ys IHys].
  重写 eq_sym.
  情况分析 E: (eq_dec y x); 首先精确。
  move/IHys => Hsub {IHys}.
  精确: sublist_cons_add.
Qed.

引理 all_xpredT_true : 对于所有 a 和 (xs : list a)，都有 all xpredT xs。
证明。通过 move=> ?; 消去。证毕。

Lemma between_all_cat : 对于所有类型 a 的 a (xs ys : 列表 a) 和关系 R : rel a,
  between_all R (xs ++ ys) =
  [&& between_all R xs
  ,   between_all R ys
  ,   all (fun x => all (R x) ys) xs
  &   all (fun y => all (R ^~ y) xs) ys
  ]。
证明。
  move=> a xs ys R。
  消元: xs => [|x xs IHxs] 在 ys * 中。
    通过重写 /= all_xpredT_true Bool.andb_true_r。
  重写 cat_cons all_all_cons。
  重写 /= all_cat {}IHxs /=。
  重写 !andbA; f_equal。
  重写 [X in _ = X]andbC。
  重写 !andbA; f_equal。
  重写 [X in _ = X]andbC。
  重写 !andbA; f_equal。
  重写 Bool.andb_diag。
  通过重写 -!andbA and_swap。
证毕。

在所有范畴C之间的引理 {a} (xs ys : 列表 a) (R : 关系 a) (_ : 对称 R) :
  between_all R (xs ++ ys) = between_all R (ys ++ xs).
证明.
  归纳法: xs => /= [|x xs IHxs] 在 ys * 中.
    通过重写 cats0 得出.
  重写 IHxs.
  归纳法: ys => /= [|y ys IHys].
    通过重写 cats0 得出.
  重写 -IHys !andbA.
  一致 (_ && _).
  重写 !all_cat -!andbA 2!andbA and_swap.
  一致 (_ && _).
  重写 andbC -!andbA [RHS]and_swap.
  一致 (_ && _).
  重写 [RHS]and_swap.
  一致 (_ && _).
  通过重写 H 得出.
证毕.

引理 allpairs_map ：
  对于所有 a b c （f : a → b → c） （xs : list a） （ys : list b），
  [list f x y | x <- xs, y <- ys] =
  flatten [list [list f x y | y <- ys] | x <- xs].
证明。
  移动=> a b c f。
  消去=> //= [x xs IHxs] y。
  一致 (_ ++ _)。
  精确：IHxs。
Qed。
*)

Lemma StronglySorted_impl :
  forall (A : Type) (P Q : A → A → Prop),
    (forall a b : A, P a b → Q a b) ->
      forall l : list A, StronglySorted P l → StronglySorted Q l.
Proof.
  intros.
  induction l; simpl.
  - constructor.
  - constructor.
    + apply IHl.
      inversion H0; assumption.
    + inversion H0; subst.
      apply Forall_impl with (P:=P a).
      * apply H.
      * assumption.
Qed.

(*
Permutation infrastructure for the insertion-sort helpers below.  [Permutation]
   is the equivalence on lists that quotients [app] down to the free *commutative*
   monoid; registering it as an [Equivalence] (with [insert] and [Forall] shown to
   respect it) lets the sorting lemmas rewrite freely under reordering.  Coq's
   [Permutation] is reflexive by construction, so only symmetry and transitivity
   need discharging here.

--------
用于下面插入排序辅助函数的置换基础设施。[Permutation] 是列表上的等价，用于将 [app] 商化为自由 *交换* 幺半群；将其注册为 [Equivalence]（并显示 [insert] 和 [Forall] 尊重它）可以让排序引理在重新排序时自由重写。Coq 的 [Permutation] 由构造上是自反的，因此这里只需要处理对称性和传递性。
*)
#[export]
Program Instance Permutation_Equivalence {A} : Equivalence (@Permutation A).
Next Obligation. now apply (@Permutation_sym A). Qed.
Next Obligation. now eapply (@Permutation_trans A); eauto. Qed.

#[export]
Program Instance Permutation_insert_mor {A} :
  Proper ((@eq A ==> @eq A ==> @eq bool)
            ==> @eq A
            ==> @Permutation A
            ==> @Permutation A) (@insert A).
Next Obligation.
  generalize dependent y.
  generalize dependent x.
  induction H; subst;
  unfold insert; simpl; intros; fold @insert.
  - constructor; trivial.
  - rewrite (X _ _ eq_refl _ _ eq_refl).
    destruct (y x x0); simpl.
    + constructor.
      apply IHPermutation; trivial.
    + constructor; constructor.
      exact H.
  - rewrite !(X _ _ eq_refl _ _ eq_refl).
    destruct (y0 y x0);
    destruct (y0 x x0); simpl.
    + rewrite perm_swap.
      constructor.
      constructor.
      induction l; simpl;
      unfold insert; simpl; intros; fold @insert.
      * constructor; constructor.
      * rewrite (X _ _ eq_refl _ _ eq_refl).
        destruct (y0 a x0); simpl.
        ** constructor.
           exact IHl.
        ** reflexivity.
    + rewrite perm_swap.
      constructor.
      rewrite perm_swap.
      reflexivity.
    + symmetry.
      rewrite perm_swap.
      constructor.
      rewrite perm_swap.
      reflexivity.
    + constructor.
      rewrite perm_swap.
      reflexivity.
  - rewrite IHPermutation1.
    + apply IHPermutation2.
      apply X.
    + reflexivity.
Qed.

#[export]
Program Instance Permutation_Forall_mor {A} :
  Proper ((@eq A ==> @eq Prop)
            ==> @Permutation A
            ==> iff) (@Forall A).
Next Obligation.
  split; intros.
  - apply Forall_impl with (P:=x).
    + intros z H1.
      rewrite (X z z eq_refl) in H1.
      assumption.
    + induction H; simpl; trivial.
      * constructor.
        ** inversion H0; subst; trivial.
        ** apply IHPermutation.
          inversion H0; trivial.
      * inversion H0; subst.
        inversion H3; subst.
        intuition.
      * intuition.
  - apply List.Forall_impl with (P:=y).
    + intros z H2.
      rewrite (X z z eq_refl).
      assumption.
    + induction H; simpl; trivial.
      * constructor.
        ** inversion H0; subst; trivial.
        ** apply IHPermutation.
           inversion H0; trivial.
      * inversion H0; subst.
        inversion H3; subst.
        intuition.
      * intuition.
Qed.

Lemma Permutation_insert : forall A (a : A) R xs ys,
  Permutation xs ys → Permutation (insert R a xs) (a :: ys).
Proof.
  intros.
  rewrite <- H; clear H.
  induction xs; intros; simpl.
  - constructor; trivial.
  - unfold insert.
    destruct (R a0 a) eqn:Heqe;
    fold@insert.
    + rewrite perm_swap.
      constructor.
      exact IHxs.
    + reflexivity.
Qed.

Lemma Permutation_sortBy : forall A (a : A) (R : A → A → bool) xs,
  Permutation (sortBy R xs) xs.
Proof.
  induction xs; intros; simpl.
  - constructor.
  - apply Permutation_insert.
    exact IHxs.
Qed.

Lemma Permutation_Forall : forall A (P : A → Prop) (xs ys : list A),
  Permutation xs ys
    → List.Forall P xs
    → List.Forall P ys.
Proof.
  intros.
  rewrite <- H.
  assumption.
Qed.

Lemma Forall_insert : forall a (R : a → a → Prop) (Q : a → a → bool) x xs y,
  Q x y = true
    → (forall a b, R a b <-> Q a b = true)
    → List.Forall (R x) xs
    → List.Forall (R x) (insert Q y xs).
Proof.
  intros.
  apply Permutation_Forall with (xs:=y :: xs).
  - symmetry.
    apply Permutation_insert.
    reflexivity.
  - constructor; trivial.
    apply H0.
    assumption.
Qed.

Lemma StronglySorted_insert :
  forall a (R : a → a → Prop) (Q : a → a → bool)
         `{Transitive _ R} x xs,
    (forall y, Q y x = false → Q x y = true)
      → (forall a b, R a b <-> Q a b = true)
      → StronglySorted R xs
      → StronglySorted R (insert Q x xs).
Proof.
  intros a R Q H x xs H1 H2 H3.
  generalize dependent x.
  induction xs as [|y ys IHys]; intros; simpl.
  - unfold insert.
    constructor; constructor.
  - unfold insert.
    destruct (Q y x) eqn:E;
    fold @insert.
    + constructor.
      * apply IHys; trivial.
        inversion H3; trivial.
      * apply Forall_insert; trivial.
        inversion H3; trivial.
    + constructor; trivial.
      constructor.
      * apply H2; trivial.
        inversion H3.
        apply H1 in E.
        assumption.
      * apply H1 in E.
        apply H2 in E.
        apply (@Forall_ordered a R H x y ys E).
        inversion H3.
        assumption.
Qed.

Lemma sortBy_sorted : forall a (R : a → a → Prop) (Q : a → a → bool)
                             `{Transitive _ R} xs,
  (forall x y, Q y x = false → Q x y = true)
    → (forall a b, R a b <-> Q a b = true)
    → StronglySorted R (sortBy Q xs).
Proof.
  intros a R Q H xs H1 H2.
  induction xs as [|x xs IHxs]; simpl.
  - constructor.
  - apply StronglySorted_insert; trivial.
    exact (H1 x).
Qed.

(*
The lawful functor instance: [list] is a genuine endofunctor on [Coq],
   with [fmap = List.map].  As in the sibling [Maybe]/[Either]/[Tuple] proof
   files, the witness reuses the source [list_Functor] instance for [a_fmap]
   and discharges the three [AFunctor] obligations -- [map] respects pointwise
   equality of functions, [map id = id], and [map (g ∘ f) = map g ∘ map f] --
   each by induction on the list.  (The name reuses the source [list_Functor]
   instance from [Theory.Coq.List].)

--------
合法函子实例：[list] 是 [Coq] 上的一个真正的自函子，带有 [fmap = List.map]。与兄弟 [Maybe]/[Either]/[Tuple] 证明文件一样，该证据重用 [list_Functor] 的源实例用于 [a_fmap]，并完成三个 [AFunctor] 的义务——[map] 尊重函数的逐点相等，[map id = id] 和 [map (g ∘ f) = map g ∘ map f]——每个都通过对列表进行归纳来完成。（该名称重用 [Theory.Coq.List] 中的源 [list_Functor] 实例。）
*)
Program Definition list_Functor : IsFunctor list_Functor := {|
  a_fmap := list_Functor;
|}.
Next Obligation.
  proper.
  induction x1; simpl; congruence.
Qed.
Next Obligation.
  induction x0; simpl; congruence.
Qed.
Next Obligation.
  induction x0; simpl; congruence.
Qed.
