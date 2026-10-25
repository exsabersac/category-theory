(* * A theory of type-aligned lists, using the Coq-Equations plugin / * 类型对齐列表的理论，使用 Coq-Equations 插件 *)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.

Set Transparent Obligations.

Open Scope lazy_bool_scope.

(*
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/Quiver_(mathematics)

 A [netlist B i j] is a NON-Empty Typed list: a type-aligned sequence of
 values of [B] whose adjacent indices line up, [B i j0], [B j0 j1], ...,
 [B jn j].  Reading [B] as the hom-family of a quiver (directed graph) on
 the index type [A], such a chain is exactly a non-empty PATH in that
 quiver, i.e. a composable chain of edges/morphisms from [i] to [j].  These
 are the (length >= 1) morphisms of the free category / path category on
 the quiver [B].

 The "NET" prefix abbreviates "Non-Empty Typed": [tfin] is a one-edge path
 and [tadd] prepends an edge, so a netlist always carries at least one edge
 (there is no nil constructor).  The same data structure is known in the
 Haskell community as a non-empty "type-aligned sequence" (Atze van der
 Ploeg, https://github.com/atzeus/type-aligned).

 Operations below give this family its path algebra: [netlist_app] (++++)
 concatenates two head-to-tail composable paths and is associative
 ([netlist_app_assoc]), making [netlist B] an [ISemigroup] (a category
 without identities, i.e. a semicategory) at the end of the file.  The
 remaining operations are the expected destructors (head/tail/init/last,
 uncons), structural maps ([netlist_map] over the edge family, [netlist_mapv]
 to a plain list), [netlist_rev] (reverse, given an edge-flipping operation),
 [netlist_concat] (flatten a path of paths), and decidable structure
 (equality, setoid equivalence, and the [netlist_incl] / [netlist_find_sublist]
 sub-path searches) used when [A] and each [B i j] have decidable equality.
 Formalized with the Equations plugin, with UIP enabled so dependent matches
 on the index equalities reduce. 

 --------
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/Quiver_(mathematics)

 [netlist B i j] 是 NON-Empty Typed list：一组类型对齐的 [B] 值序列，相邻下标衔接，形如 [B i j0]、[B j0 j1]、…、[B jn j]。把 [B] 读作指标类型 [A] 上 quiver 的 hom 族时，这样的链恰是该 quiver 中从 [i] 到 [j] 的非空路径，即可复合的边/态射链。它们是 quiver [B] 上自由范畴 / 路径范畴中长度 ≥ 1 的态射。

 前缀 “NET” 表示 “Non-Empty Typed”：[tfin] 是单边路径，[tadd] 前置一边，故 netlist 总至少含一边（无 nil 构造子）。同一数据结构在 Haskell 社区称为非空 “type-aligned sequence”（Atze van der Ploeg, https://github.com/atzeus/type-aligned）。

 下文运算给出该族的路径代数：[netlist_app] (++++) 拼接首尾可接路径且结合（[netlist_app_assoc]），使 [netlist B] 在文件末成为 [ISemigroup]（无恒等的范畴，即半范畴）。其余是预期消去（head/tail/init/last、uncons）、结构映射（沿边族的 [netlist_map]、到普通列表的 [netlist_mapv]）、[netlist_rev]（给定翻边的反转）、[netlist_concat]（展平路径的路径），以及在 [A] 与各 [B i j] 可判定相等时使用的可判定结构（相等、setoid 等价，以及 [netlist_incl]/[netlist_find_sublist] 子路径搜索）。用 Equations 插件形式化，启用 UIP 使指标相等上的依赖匹配可化简。
*)

Inductive netlist {A : Type} (B : A → A → Type) : A → A → Type :=
  (*
 [tfin x] is the singleton path consisting of one edge [x : B i j];
 [tadd j x xs] prepends an edge [x : B i j] onto a path [xs : B j k],
 yielding a path [B i k].  There is no nil case, so every path is
 non-empty. 

 --------
 [tfin x] 是由单边 [x : B i j] 组成的单点路径；
 [tadd j x xs] 把边 [x : B i j] 前置到路径 [xs : B j k]，得到路径 [B i k]。无 nil 情形，故每条路径非空。
*)
  | tfin : ∀ i j : A, B i j → netlist i j
  | tadd : ∀ i j k : A, B i j → netlist j k → netlist i k.

Derive Signature NoConfusion NoConfusionHom Subterm for netlist.

Arguments tfin {A B i j} x.
Arguments tadd {A B i} j {k} _ _.

Notation "x :::: xs" := (tadd _ x xs) (at level 60, right associativity).

Section Netlist.

Context {A : Type}.
Context {B : A → A → Type}.

Fixpoint netlist_length {i j} (xs : netlist B i j) : nat :=
  match xs with
  | tfin _ => 1
  | tadd _ _ xs => 1 + netlist_length xs
  end.

Equations netlist_app {i j k} (xs : netlist B i j) (ys : netlist B j k) :
  netlist B i k :=
  netlist_app (tfin x) ys := x :::: ys;
  netlist_app (@tadd _ _ _ x xs) ys := x :::: netlist_app xs ys.

Notation "xs ++++ ys" := (netlist_app xs ys) (at level 60, right associativity).

Equations netlist_uncons {i j} (xs : netlist B i j) :
  { z : A & B i z & option (netlist B z j) }%type :=
  netlist_uncons (tfin x) := existT2 _ _ _ x None;
  netlist_uncons (@tadd _ _ _ x xs) := existT2 _ _ _ x (Some xs).

Equations netlist_map {i j A' C} {f : A → A'}
          (g : ∀ i j : A, B i j → C (f i) (f j))
          (xs : netlist B i j) : netlist C (f i) (f j) :=
  netlist_map g (tfin x) := tfin (g _ _ x);
  netlist_map g (@tadd _ _ _ x xs) := g _ _ x :::: netlist_map g xs.

Import ListNotations.

Equations netlist_mapv {i j C}
          (g : ∀ i j : A, B i j → C)
          (xs : netlist B i j) : list C :=
  netlist_mapv g (tfin x) := [g _ _ x];
  netlist_mapv g (@tadd _ _ _ x xs) := g _ _ x :: netlist_mapv g xs.

Equations netlist_head {i j} (xs : netlist B i j) :
  { z : A & B i z }%type :=
  netlist_head (tfin x) := (_; x);
  netlist_head (@tadd _ _ _ x _) := (_; x).

Equations netlist_tail {i j} (xs : netlist B i j) :
  option { z : A & netlist B z j }%type :=
  netlist_tail (tfin _) := None;
  netlist_tail (@tadd _ _ _ _ xs) := Some (_; xs).

Equations netlist_init {i j} (xs : netlist B i j) :
  option { z : A & netlist B i z }%type :=
  netlist_init (tfin _) := None;
  netlist_init (@tadd _ _ _ x xs) with netlist_init xs := {
    | None => Some (_; tfin x);
    | Some (existT ys) => Some (_; (x :::: ys))
  }.

Equations netlist_last {i j} (xs : netlist B i j) :
  { z : A & B z j }%type :=
  netlist_last (tfin x) := (_; x);
  netlist_last (@tadd _ _ _ _ xs) := netlist_last xs.

Equations netlist_rev (flip : ∀ x y : A, B x y → B y x)
          {i j} (xs : netlist B i j) : netlist B j i :=
  netlist_rev flip (tfin x) := tfin (flip _ _ x);
  netlist_rev flip (@tadd _ _ _ x xs) :=
    netlist_rev flip xs ++++ tfin (flip _ _ x).

Equations netlist_concat {i j} (xs : netlist (netlist B) i j) : netlist B i j :=
  netlist_concat (tfin x) := x;
  netlist_concat (@tadd _ _ _ x xs) := x ++++ netlist_concat xs.

Context `{EqDec A}.
Context `{∀ i j, EqDec (B i j)}.

Import EqNotations.

(*
 Decides whether the path [xs] occurs as a sub-path of [ys]: a run of
 consecutive edges of [ys], with matching endpoints, equal (via [eq_dec])
 edge-by-edge to [xs].  The index equalities [eq_dec] produces are used to
 [rew]-transport the candidate edge of [ys] into [B]'s expected fibre before
 comparing.  Requires decidable equality on both [A] and each [B i j].
 [netlist_find_sublist] below is the proof-carrying analogue, returning the
 surrounding prefix/suffix instead of a mere boolean. 

 --------
 判定路径 [xs] 是否作为 [ys] 的子路径出现：即 [ys] 上一串连续边，端点匹配，并经 [eq_dec] 逐边等于 [xs]。[eq_dec] 产生的指标相等用于把 [ys] 的候选边 [rew]-传送到 [B] 的期望纤维后再比较。要求 [A] 与各 [B i j] 皆可判定相等。下文 [netlist_find_sublist] 是携带证明的对应物，返回周围前缀/后缀而非单纯布尔。
*)
Equations netlist_incl
          {j k} (xs : netlist B j k)
          {i l} (ys : netlist B i l) : bool :=
  netlist_incl (@tfin _ _ j k x) (@tfin _ _ i l y)
    with (eq_dec j i, eq_dec k l) := {
      | pair (left H1) (left H2)
        with eq_dec x (rew <- [fun y => B _ y] H2 in
                     rew <- [fun x => B x _] H1 in y) := {
          | left _ => true;
          | _ => false
        };
      | _ => false
    };
  netlist_incl (@tfin _ _ j k x) (@tadd _ _ i o _ y ys)
    with (eq_dec j i, eq_dec k o) := {
      | pair (left H1) (left H2)
        with eq_dec x (rew <- [fun y => B _ y] H2 in
                     rew <- [fun x => B x _] H1 in y) := {
          | left _ => true;
          | _ => false
        };
      | _ => netlist_incl (tfin x) ys
    };
  netlist_incl _ (tfin _) := false;
  netlist_incl (@tadd _ _ j m _ x xs) (@tadd _ _ i o _ y ys)
    with (eq_dec j i, eq_dec m o) := {
      | pair (left H1) (left H2) =>
        (eq_dec x (rew <- [fun y => B _ y] H2 in
                   rew <- [fun x => B x _] H1 in y)
           &&& netlist_incl xs ys)
          ||| netlist_incl (x :::: xs) ys;
      | _ => netlist_incl (x :::: xs) ys
    }.

Equations netlist_eq_dec {i j : A} (x y : netlist B i j) : {x = y} + {x ≠ y} :=
  netlist_eq_dec (tfin x) (tfin y) with eq_dec x y := {
    | left _ => in_left;
    | _ => in_right
  };
  netlist_eq_dec (@tfin _ _ _) _ := in_right;
  netlist_eq_dec _ (@tfin _ _ _) := in_right;
  netlist_eq_dec (@tadd _ _ _ m _ x xs) (@tadd _ _ _ o _ y ys)
    with eq_dec m o := {
      | left H with eq_dec x (rew <- [fun x => B _ x] H in y) := {
          | left _ with netlist_eq_dec xs (rew <- [fun x => netlist B x _] H in ys) := {
             | left _ => in_left;
             | _ => in_right
            };
          | _ => in_right
        };
      | _ => in_right
    }.
Next Obligation.
  simpl_eq; intros.
  apply n.
  inv H1.
  apply Eqdep_dec.inj_pair2_eq_dec in H3; [|apply eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H3; [|apply eq_dec].
  assumption.
Defined.
Next Obligation.
  simpl_eq; intros.
  intuition eauto.
  match goal with [ H : _ → False |- _ ] => apply H end.
  inv H1.
  apply Eqdep_dec.inj_pair2_eq_dec in H3; [|apply eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H3; [|apply eq_dec].
  assumption.
Defined.
Next Obligation.
  simpl_eq; intros.
  intuition eauto.
  match goal with [ H : _ → False |- _ ] => apply H end.
  inv H1.
  apply Eqdep_dec.inj_pair2_eq_dec in H3; [|apply eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H3; [|apply eq_dec].
  assumption.
Defined.

Lemma netlist_app_comm_cons {i j k l} (x : B i j)
      (xs : netlist B j k) (ys : netlist B k l) :
  x :::: (xs ++++ ys) = (x :::: xs) ++++ ys.
Proof. now rewrite netlist_app_equation_2. Qed.

Lemma netlist_app_assoc {i j k l}
      (xs : netlist B i j) (ys : netlist B j k) (zs : netlist B k l) :
  (xs ++++ ys) ++++ zs = xs ++++ (ys ++++ zs).
Proof.
  induction xs; auto.
  now rewrite <- !netlist_app_comm_cons, IHxs.
Qed.

Context `{∀ i j, Setoid (B i j)}.

Equations netlist_equiv {i j : A} (x y : netlist B i j) : Type :=
  netlist_equiv (@tfin _ _ x) (@tfin _ _ y) := x ≈ y;
  netlist_equiv (@tfin _ _ _) _ := False;
  netlist_equiv _ (@tfin _ _ _) := False;
  netlist_equiv (@tadd _ _ _ m _ x xs) (@tadd _ _ _ o _ y ys)
    with eq_dec m o := {
      | left H =>
         equiv x (rew <- [fun x => B _ x] H in y) *
         netlist_equiv xs (rew <- [fun x => netlist B x _] H in ys);
      | right _ => False
    }.

#[export] Program Instance netlist_equiv_Equivalence {i j} :
  Equivalence (@netlist_equiv i j).
Next Obligation.
  repeat intro.
  induction x; simpl.
  - rewrite netlist_equiv_equation_1.
    reflexivity.
  - rewrite netlist_equiv_equation_4.
    rewrite EqDec.peq_dec_refl.
    split.
    + apply Equivalence_Reflexive.
    + apply IHx.
Qed.
Next Obligation.
  repeat intro.
  induction x; simpl.
  - dependent elimination y as [tfin _]; auto.
    rewrite netlist_equiv_equation_1 in *.
    now symmetry.
  - dependent elimination y as [tadd _ y ys]; auto.
    rewrite netlist_equiv_equation_4 in *.
    destruct (eq_dec j _); [|contradiction].
    subst.
    rewrite EqDec.peq_dec_refl.
    destruct X.
    split.
    + now apply Equivalence_Symmetric.
    + apply IHx, n.
Qed.
Next Obligation.
  repeat intro.
  induction x; simpl.
  - dependent elimination y as [tfin _]; auto.
    induction z; simpl.
    + rewrite netlist_equiv_equation_1 in *.
      now etransitivity; eauto.
    + now rewrite netlist_equiv_equation_2.
  - dependent elimination y as [tadd _ y ys]; auto.
    simpl; intros.
    dependent elimination z as [tadd _ z zs]; auto.
    rewrite netlist_equiv_equation_4 in *.
    destruct (eq_dec j _); [|contradiction].
    destruct (eq_dec _ _); [|contradiction].
    subst.
    rewrite EqDec.peq_dec_refl.
    destruct X, X0.
    split.
    + transitivity y; auto.
    + eapply IHx; eauto.
Qed.

#[export] Program Instance netlist_Setoid {i j} : Setoid (netlist B i j) := {
  equiv := netlist_equiv;
  setoid_equiv := netlist_equiv_Equivalence;
}.

#[export] Program Instance netlist_cons_respects {i j k} :
  Proper (equiv ==> equiv ==> equiv) (@tadd A B i j k).
Next Obligation.
  repeat intro.
  simpl in *.
  rewrite netlist_equiv_equation_4.
  now rewrite EqDec.peq_dec_refl.
Qed.

#[export] Program Instance netlist_app_respects {i j k} :
  Proper (equiv ==> equiv ==> equiv) (@netlist_app i j k).
Next Obligation.
  repeat intro.
  generalize dependent k.
  induction x; intros; dependent elimination y.
  - rewrite !netlist_app_equation_1.
    rewrite netlist_equiv_equation_1 in X.
    now rewrite X, X0.
  - contradiction.
  - contradiction.
  - rewrite <- !netlist_app_comm_cons.
    rewrite netlist_equiv_equation_4 in *.
    unfold netlist_equiv_clause_4 in *.
    destruct (eq_dec j j1); [|contradiction].
    subst.
    destruct X.
    split; auto.
    apply IHx.
    + exact n0.
    + exact X0.
Qed.

#[export] Program Instance netlist_EqDec {i j} : @EqDec (netlist B i j) := {
  eq_dec := netlist_eq_dec
}.

End Netlist.

Notation "xs ++++ ys" := (netlist_app xs ys) (at level 60, right associativity).

Section NetlistProofs.

Context {A : Type}.
Context {B : A → A → Type}.

Lemma netlist_app_length {i j k} (xs : netlist B i j) (ys : netlist B j k) :
  netlist_length (xs ++++ ys) = (netlist_length xs + netlist_length ys)%nat.
Proof.
  induction xs; auto.
  rewrite <- netlist_app_comm_cons; simpl.
  now rewrite IHxs.
Qed.

Lemma netlist_concat_tadd {i j k} (x : netlist B i j) (xs : netlist (netlist B) j k) :
  netlist_concat (x :::: xs) = x ++++ netlist_concat xs.
Proof. reflexivity. Qed.

End NetlistProofs.

Lemma netlist_concat_app {A : Type} {B : A → A → Type} {i j k}
      (xs : netlist (netlist B) i j) (ys : netlist (netlist B) j k) :
  netlist_concat (xs ++++ ys) = netlist_concat xs ++++ netlist_concat ys.
Proof.
  induction xs; auto.
  rewrite <- netlist_app_comm_cons; simpl.
  rewrite !netlist_concat_equation_2.
  rewrite IHxs.
  now rewrite netlist_app_assoc.
Qed.

Section NetlistProofsRev.

Context {A : Type}.
Context {B : A → A → Type}.

Variables flip : ∀ x y : A, B x y → B y x.

Lemma netlist_rev_unit {i j k} (xs : netlist B i j) (x : B j k) :
  netlist_rev flip (xs ++++ tfin x) = flip _ _ x :::: netlist_rev flip xs.
Proof.
  induction xs; auto; simpl.
  rewrite <- netlist_app_comm_cons; simpl.
  rewrite netlist_rev_equation_2.
  now rewrite IHxs.
Qed.

Lemma netlist_rev_app_distr {i j k} (xs : netlist B i j) (ys : netlist B j k) :
  netlist_rev flip (xs ++++ ys) = netlist_rev flip ys ++++ netlist_rev flip xs.
Proof.
  generalize dependent i.
  induction xs; simpl; intros; auto.
  rewrite <- netlist_app_comm_cons; simpl.
  rewrite !netlist_rev_equation_2.
  rewrite IHxs.
  now rewrite <- netlist_app_assoc.
Qed.

Hypothesis flip_involutive : ∀ (i j : A) (x : B i j),
  flip _ _ (flip _ _ x) = x.

Lemma netlist_rev_involutive {i j} (xs : netlist B i j) :
  netlist_rev flip (netlist_rev flip xs) = xs.
Proof using A B flip flip_involutive.
  induction xs; simpl; auto.
  - rewrite !netlist_rev_equation_1.
    now rewrite flip_involutive.
  - rewrite netlist_rev_equation_2.
    rewrite netlist_rev_app_distr.
    rewrite IHxs.
    rewrite netlist_rev_equation_1.
    now rewrite flip_involutive.
Qed.

Lemma netlist_rev_length {i j} (xs : netlist B i j) :
  netlist_length (netlist_rev flip xs) = netlist_length xs.
Proof.
  induction xs; auto; simpl.
  rewrite netlist_rev_equation_2.
  rewrite netlist_app_length, IHxs; simpl.
  apply PeanoNat.Nat.add_1_r.
Qed.

End NetlistProofsRev.

Section NetlistProofsInj.

(*
 Dependending on the choice of A, this can be either
 Eqdep.EqdepTheory.inj_pair2  (incurs axiom)
 or Eqdep_dec.inj_pair2_eq_dec   (when A is decidable)

 --------
 取决于 A 的选取，这可以是 Eqdep.EqdepTheory.inj_pair2（引入公理），或 Eqdep_dec.inj_pair2_eq_dec（当 A 可判定时）。
*)
Hypothesis inj_pair2 :
  ∀ (U : Type) (P : U → Type) (p : U) (x y : P p),
    (p; x) = (p; y) → x = y.

Context {A : Type}.
Context {B : A → A → Type}.

Lemma netlist_cons_uncons
      {i m j} (xs : netlist B i j) (y : B i m) ys :
  netlist_uncons xs = existT2 _ _ _ y (Some ys) → xs = y :::: ys.
Proof using A B inj_pair2.
  destruct xs; simpl; intros.
  - inversion H.
  - inversion H; subst; clear H.
    apply inj_pair2 in H2; auto.
    apply inj_pair2 in H3; auto.
    now rewrite H2, H3.
Qed.

End NetlistProofsInj.

Section Sublist.

Context {A : Type}.
Context {B : A → A → Type}.

Context `{EqDec A}.
Context `{∀ i j, EqDec (B i j)}.

Import EqNotations.

(*
 Searches for the path [xs : B j k] as a sub-path of [ys : B i l].  On
 success returns the surrounding context as [Some (pre, post)], where each
 side is either the corresponding prefix/suffix path or a proof that no edges
 remain on that side (the index already matches: [i = j] on the left, [k = l]
 on the right).  [netlist_find_sublist_app] proves this output is faithful:
 [ys] equals [pre ++++ xs ++++ post] (up to the [rew] transports recorded by
 the [i = j] / [k = l] equalities).  This is the proof-carrying refinement of
 the boolean [netlist_incl]. 

 --------
 在 [ys : B i l] 中搜索子路径 [xs : B j k]。成功时返回周围上下文 [Some (pre, post)]，每一侧或为对应前缀/后缀路径，或为该侧已无边的证明（指标已匹配：左侧 [i = j]，右侧 [k = l]）。[netlist_find_sublist_app] 证明此输出忠实：[ys] 等于 [pre ++++ xs ++++ post]（至多差 [i = j]/[k = l] 所记录的 [rew] 传送）。这是布尔 [netlist_incl] 的携带证明精细化。
*)
Fixpoint netlist_find_sublist
         {j k} (xs : netlist B j k)
         {i l} (ys : netlist B i l) :
  option ((netlist B i j + { i = j}) *
          (netlist B k l + { k = l})) :=
  match xs, ys with
  | @tfin _ _ j k x, @tfin _ _ i l y =>
    match eq_dec i j, eq_dec k l with
    | left H1, left H2 =>
      match eq_dec x (rew <- [fun y => B _ y] H2 in
                      rew [fun x => B x _] H1 in y) with
      | left _ => Some (inright H1, inright H2)
      | _ => None
      end
    | _, _ => None
    end
  | @tfin _ _ j k x, @tadd _ _ i o _ y ys =>
    match eq_dec i j, eq_dec k o with
    | left H1, left H2 =>
      match eq_dec x (rew <- [fun y => B _ y] H2 in
                      rew [fun x => B x _] H1 in y) with
      | left _ =>
        Some (inright H1,
              inleft (rew <- [fun x => netlist B x _] H2 in ys))
      | _ => None
      end
    | _, _ =>
      match netlist_find_sublist (tfin x) ys with
      | None => None
      | Some (inright H, zs) =>
        Some (inleft (rew [fun y => netlist B _ y] H in tfin y), zs)
      | Some (inleft ys, zs) =>
        Some (inleft (y :::: ys), zs)
      end
    end
  | _, tfin _ => None
  | @tadd _ _ j m k x xs, @tadd _ _ i o l y ys =>
    match eq_dec i j, eq_dec m o with
    | left H1, left H2 =>
      match eq_dec x (rew [fun x => B x _] H1 in
                      rew <- [fun x => B _ x] H2 in y) with
      | left _ =>
        match netlist_find_sublist xs ys with
        | Some (inright H, cs) =>
          Some (inright H1, cs)
        | _ =>
          match netlist_find_sublist (x :::: xs) ys with
          | None => None
          | Some (inright H, zs) =>
            Some (inleft (rew [fun y => netlist B _ y] H in tfin y), zs)
          | Some (inleft ys, zs) =>
            Some (inleft (y :::: ys), zs)
          end
        end
      | _ =>
        match netlist_find_sublist (x :::: xs) ys with
        | None => None
        | Some (inright H, zs) =>
          Some (inleft (rew [fun y => netlist B _ y] H in tfin y), zs)
        | Some (inleft ys, zs) =>
          Some (inleft (y :::: ys), zs)
        end
      end
    | _, _  =>
      match netlist_find_sublist (x :::: xs) ys with
      | None => None
      | Some (inright H, zs) =>
        Some (inleft (rew [fun y => netlist B _ y] H in tfin y), zs)
      | Some (inleft ys, zs) =>
        Some (inleft (y :::: ys), zs)
      end
    end
  end.

End Sublist.

Section SublistProofsInj.

Context {A : Type}.
Context {B : A → A → Type}.

Context `{EqDec A}.
Context `{∀ i j, EqDec (B i j)}.

Import EqNotations.

Open Scope signature_scope.

Ltac cleanup H post IHf Heqo :=
  inv H;
  specialize (IHf _ _ _ _ _ Heqo); simpl in IHf;
  destruct post; subst;
  try rewrite netlist_app_comm_cons.

Lemma netlist_find_sublist_app
      {j k} (g : netlist B j k)
      {i l} (f : netlist B i l) {pre post} :
  netlist_find_sublist g f = Some (pre, post)
      → match pre, post with
         | inright H1, inright H2  =>
           f = rew <- [fun x => netlist B x _] H1 in
               rew [fun x => netlist B _ x] H2 in g
         | inleft pre, inright H2  =>
           f = pre ++++ rew [fun x => netlist B _ x] H2 in g
         | inright H1, inleft post =>
           f = rew <- [fun x => netlist B x _] H1 in g ++++ post
         | inleft pre, inleft post =>
           f = pre ++++ g ++++ post
         end.
Proof.
  intros.
  generalize dependent k.
  generalize dependent j.
  induction f; intros; simpl in H1.
  - destruct g.
    + destruct (eq_dec i i0); [|discriminate]; subst.
      destruct (eq_dec j0 j); [|discriminate]; subst.
      destruct (eq_dec b0 _); [|discriminate]; subst.
      inversion H1; now subst.
    + discriminate.
  - destruct g.
    + destruct (eq_dec i i0); subst.
      * destruct (eq_dec j0 j); subst.
        ** destruct (eq_dec b0 _); [|discriminate]; subst.
           inversion H1; now subst.
        ** destruct (netlist_find_sublist _ _) eqn:?; [|discriminate].
           destruct p.
           destruct s; subst;
           now cleanup H1 post IHf Heqo.
      * destruct (netlist_find_sublist _ _) eqn:?; [|discriminate].
        destruct p.
        destruct s; subst;
        now cleanup H1 post IHf Heqo.
    + destruct (eq_dec i i0); subst. {
        destruct (eq_dec j0 j); subst. {
          destruct (eq_dec b0 _). {
            subst.
            destruct (netlist_find_sublist g f) eqn:?. {
              destruct p.
              destruct s; subst.
              - simpl_eq.
                destruct (netlist_find_sublist (_ :::: g) f) eqn:?; [|discriminate].
                destruct p.
                destruct s; subst;
                now cleanup H1 post IHf Heqo0.
              - cleanup H1 post IHf Heqo; auto;
                simpl_eq;
                now dependent elimination e.
            }
            destruct (netlist_find_sublist (_ :::: g) f) eqn:?; [|discriminate].
            destruct p.
            destruct s; subst;
            now cleanup H1 post IHf Heqo0; auto.
          }
          destruct (netlist_find_sublist (_ :::: g) f) eqn:?; [|discriminate].
          destruct p.
          destruct s; subst;
          now cleanup H1 post IHf Heqo; auto.
        }
        destruct (netlist_find_sublist (_ :::: g) f) eqn:?; [|discriminate].
        destruct p.
        destruct s; subst;
        now cleanup H1 post IHf Heqo; auto.
      }
      destruct (netlist_find_sublist (_ :::: g) f) eqn:?; [|discriminate].
      destruct p.
      destruct s; subst;
      now cleanup H1 post IHf Heqo; auto.
Qed.

End SublistProofsInj.

Definition nat_triple (i j : nat) : Type := ((nat * nat) * nat)%type.

Open Scope nat_scope.

Definition my_list : netlist nat_triple 0 4 :=
  tadd 1 ((0, 1), 100)
        (tadd 2 ((1, 2), 200)
               (tadd 3 ((2, 3), 300)
                      (tfin ((3, 4), 400)))).

Example netlist_find_sublist_nat_ex1 :
  ∀ H : ∀ i j : nat, EqDec (nat_triple i j),
  @netlist_find_sublist
    nat nat_triple PeanoNat.Nat.eq_dec _
    1 3 (tadd 2 ((1, 2), 200) (tfin ((2, 3), 300)))
    0 4 my_list
    = Some (inleft (tfin ((0, 1), 100)), inleft (tfin (3, 4, 400))).
Proof.
  intros; simpl; simpl_eq.
  now rewrite !EqDec.peq_dec_refl.
Qed.

Reserved Infix "<+>" (at level 42, right associativity).

(*
 nLab: https://ncatlab.org/nlab/show/semicategory

 An indexed semigroup: an associative composition [<+>] on an index-aligned
 family [B i j], with no identities required.  This is exactly the data of a
 semicategory (a category dropping the identity laws) on the objects [A].
 [netlist B] is the free such structure: its composition is path
 concatenation [netlist_app], associative by [netlist_app_assoc]. 

 --------
 nLab: https://ncatlab.org/nlab/show/semicategory

 指标半群：在指标对齐族 [B i j] 上的结合复合 [<+>]，不要求恒等。这恰是对象 [A] 上半范畴（去掉恒等律的范畴）的数据。[netlist B] 是自由此种结构：其复合为路径拼接 [netlist_app]，结合律由 [netlist_app_assoc] 给出。
*)
Class ISemigroup {A : Type} (B : A → A → Type) := {
  isappend {i j k : A} : B i j → B j k → B i k
    where "x <+> y" := (isappend x y);

  isappend_assoc {i j k l} {x : B i j} {y : B j k} {z : B k l} :
    (x <+> y) <+> z = x <+> (y <+> z)
}.

Infix "<+>" := isappend (at level 42, right associativity).

#[export]
Instance netlist_ISemigroup {A} {B : A → A → Type} : ISemigroup (netlist B) := {
  isappend := @netlist_app A B;
  isappend_assoc := @netlist_app_assoc A B
}.
