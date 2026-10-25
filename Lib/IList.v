Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

(* * Indexed (heterogeneous) lists / * 指标（异构）列表 *)

(*
 CPDT: http://adam.chlipala.net/cpdt/html/Cpdt.DataStruct.html
 nLab: https://ncatlab.org/nlab/show/dependent+product

 An [ilist l] is an Indexed list (a heterogeneous list): given a type [A]
 and an [A]-indexed family [B : A -> Type], and a list [l = [a0; ...; an]]
 of indices, [ilist l] is the type of tuples [(b0, ..., bn)] where each
 [bi : B ai].  Successive elements may therefore have *different* types,
 unlike an ordinary homogeneous [list].  This is exactly Adam Chlipala's
 heterogeneous list ([hlist]) from "Certified Programming with Dependent
 Types"; see Solver/Reify.v, whose reification code is taken from CPDT and
 builds [ilist]s of reified morphisms.

 We follow CPDT's *recursive* (type-level computation) presentation rather
 than an inductive one: [ilist] is a [Fixpoint] producing a right-nested
 product terminated by [unit].  Because the type reduces structurally on
 [l], the projections [ilist_hd]/[ilist_tl] and the lookups [ith]/[ith_exact]
 are plain [fst]/[snd] cascades that need no equality reasoning, so every
 definition here is axiom-free even though [Set Equations With UIP] is in
 scope (it is only needed by clients such as Instance/Lambda/Sem.v, and the
 Equations-generated functions below remain "closed under the global
 context").

 Categorically, with the index type [A] viewed as a discrete category and
 [B] as a functor [A -> Set], [ilist [a0; ...; an]] is the indexed/dependent
 product of the [B ai], i.e. a finite section of [B] over the chosen
 indices.  Compare Lib/TList.v (type-aligned paths over a quiver) and
 Lib/NETList.v: those align *adjacent* indices into a chain, whereas [ilist]
 simply assigns one [B]-value to each position independently. 

 --------
 CPDT: http://adam.chlipala.net/cpdt/html/Cpdt.DataStruct.html
 nLab: https://ncatlab.org/nlab/show/dependent+product

 [ilist l] 是 Indexed list（异构列表）：给定类型 [A]、[A]-指标族 [B : A -> Type]，以及指标列表 [l = [a0; ...; an]]，[ilist l] 是元组 [(b0, ..., bn)] 的类型，其中各 [bi : B ai]。因此相继元素可以有*不同*类型，不同于普通齐次 [list]。这正是 Adam Chlipala《Certified Programming with Dependent Types》中的异构列表（[hlist]）；见 Solver/Reify.v，其具体化代码取自 CPDT 并构造具体化态射的 [ilist]。

 我们采用 CPDT 的*递归*（类型级计算）呈现而非归纳呈现：[ilist] 是产生右嵌套积并以 [unit] 收尾的 [Fixpoint]。因类型在 [l] 上结构递归化简，投影 [ilist_hd]/[ilist_tl] 与查找 [ith]/[ith_exact] 是无需相等推理的普通 [fst]/[snd] 级联，故此处每一定义皆无公理，尽管 [Set Equations With UIP] 在作用域中（它仅为 Instance/Lambda/Sem.v 等客户所需，且下文 Equations 生成的函数仍“在全局上下文下封闭”）。

 范畴上，把指标类型 [A] 视为离散范畴、[B] 视为函子 [A -> Set]，则 [ilist [a0; ...; an]] 是各 [B ai] 的指标/依赖积，即 [B] 在所选指标上的有限截面。比较 Lib/TList.v（quiver 上类型对齐路径）与 Lib/NETList.v：后者把*相邻*指标连成链，而 [ilist] 只是独立地为每个位置赋一个 [B]-值。
*)

Section ilist.

Context {A : Type}.
Context {B : A → Type}.

(*
 [ilist l] computes the right-nested product [B a0 * (B a1 * (... * unit))].
 The empty list yields [unit]; a cons prepends one [B]-typed factor. 

 --------
 [ilist l] 计算右嵌套积 [B a0 * (B a1 * (... * unit))]。空列表得 [unit]；cons 前置一个 [B]-类型因子。
*)
Fixpoint ilist (l : list A) : Type :=
  match l with
  | []      => unit
  | x :: xs => B x * ilist xs
  end.

(*
 Cons for indexed lists: prepend a [B a] head onto an [ilist l], giving an
 [ilist (a :: l)].  This is just pairing, the constructor for the product
 that [ilist (a :: l)] reduces to. 

 --------
 指标列表的 cons：把 [B a] 头前置到 [ilist l]，得到 [ilist (a :: l)]。这只是配对，即 [ilist (a :: l)] 化简所得积的构造子。
*)
Definition icons
           (a : A)
           {l : list A}
           (b : B a)
           (il : ilist l) : ilist (a :: l) :=
  (b, il).

(* The empty indexed list: [ilist []] reduces to [unit], so [inil] is [tt]. / 空指标列表：[ilist []] 化简为 [unit]，故 [inil] 为 [tt]。 *)
Definition inil : ilist [] := tt.

(*
 Get the car of an ilist.  The result type is computed from [As]: for a
 cons [a :: As'] it is [B a], and for the empty list it degenerates to
 [unit] (there is no head).  Both the type annotation and the body match on
 [As] so that [fst]/[tt] are well-typed in each branch. 

 --------
 取 ilist 的 car。结果类型由 [As] 计算：对 cons [a :: As'] 为 [B a]，对空列表退化为 [unit]（无头）。类型标注与函数体都对 [As] 匹配，使各分支中 [fst]/[tt] 良型。
*)
Definition ilist_hd {As : list A} (il : ilist As) :
  match As return ilist As → Type with
    | a :: As' => fun il => B a
    | [] => fun _ => unit
  end il :=
  match As return
        ∀ (il : ilist As),
          match As return ilist As → Type with
            | a :: As' => fun il => B a
            | [] => fun _ => unit
          end il with
    | a :: As => fun il => fst il
    | [] => fun il => tt
  end il.

(*
 Get the cdr of an ilist: the remaining [ilist As'] after dropping the
 head.  As with [ilist_hd], the return type is computed from [As] so the
 empty-list branch can fall back to [unit]. 

 --------
 取 ilist 的 cdr：去掉头后剩余的 [ilist As']。与 [ilist_hd] 一样，返回类型由 [As] 计算，空列表分支可回退到 [unit]。
*)
Definition ilist_tl {As : list A} (il : ilist As) :
  match As return ilist As → Type with
    | a :: As' => fun il => ilist As'
    | [] => fun _ => unit
  end il :=
  match As return
        ∀ (il : ilist As),
          match As return ilist As → Type with
            | a :: As' => fun il => ilist As'
            | [] => fun _ => unit
          end il with
    | a :: As => fun il => snd il
    | [] => fun il => tt
  end il.

(*
 Positional lookup (CPDT's [get]): return the [n]th element of [il].  Since
 [n] may be out of range, the caller supplies a default index [defA] with a
 witness [defB : B defA]; the result type [B (nth n As defA)] mirrors the
 default used by [List.nth], so out-of-bounds lookups return [defB].
 Defined by structural recursion on [n], descending through the tail. 

 --------
 位置查找（CPDT 的 [get]）：返回 [il] 的第 [n] 个元素。因 [n] 可能越界，调用方提供默认指标 [defA] 与见证 [defB : B defA]；结果类型 [B (nth n As defA)] 镜像 [List.nth] 所用默认，越界则返回 [defB]。对 [n] 结构递归，经尾部下沉。
*)
Definition ith (n : nat) {As : list A} (il : ilist As)
  {defA : A} (defB : B defA) : B (nth n As defA).
Proof.
  generalize dependent As.
  induction n; intros.
  - destruct As; simpl.
    + exact defB.
    + exact (fst il).
  - destruct As; simpl.
    + exact defB.
    + apply IHn.
      exact (snd il).
Defined.

(*
 Total, type-checked lookup at position [n]: with decidable equality on the
 index type [A], look up the [n]th entry and confirm its index equals the
 requested [a].  Returns [Some (b : B a)] only when both the position is in
 range and the indices match (rewriting along [eq_dec] to coerce the found
 [B a0] to [B a]); otherwise [None].  Used by Solver/Denote.v to fetch a
 reified morphism of the expected domain/codomain.  The [subst] relies only
 on [eq_dec]'s evidence, so this stays axiom-free. 

 --------
 在位置 [n] 的全、类型检查查找：当指标类型 [A] 可判定相等时，查找第 [n] 项并确认其指标等于所请求的 [a]。仅当位置在范围内且指标匹配时返回 [Some (b : B a)]（沿 [eq_dec] 改写，把找到的 [B a0] 强制为 [B a]）；否则 [None]。供 Solver/Denote.v 取期望定义域/陪域的具体化态射使用。该 [subst] 仅依赖 [eq_dec] 的证据，故保持无公理。
*)
Definition ith_exact `{EqDec A} (n : nat) (a : A)
  {As : list A} (il : ilist As) : option (B a).
Proof.
  generalize dependent As.
  induction n; intros.
  - destruct As; simpl.
    + exact None.
    + simpl in il.
      destruct (eq_dec a a0); subst.
      * exact (Some (fst il)).
      * exact None.
  - destruct As; simpl.
    + exact None.
    + simpl in il.
      destruct il.
      exact (IHn As i).
Defined.

(*
 Append two indexed lists, concatenating their index lists: the result is
 indexed by [l ++ l'], matching [List.app] on the underlying indices.
 Recurses on the first list's structure. 

 --------
 拼接两个指标列表，串联其指标表：结果以 [l ++ l'] 为指标，与底层指标上的 [List.app] 一致。对第一列表结构递归。
*)
Equations iapp `(xs : ilist l) `(ys : ilist l') : ilist (l ++ l') :=
  iapp (l:=[]) tt ys := ys;
  iapp (x, xs) ys := (x, iapp xs ys).

(*
 Inverse of [iapp]: split an [ilist (l ++ l')] back into its [ilist l] and
 [ilist l'] halves.  Note that [l] (not just [l ++ l']) must be known for
 the recursion to fire, since the split point is dictated by [l]'s length. 

 --------
 [iapp] 的逆：把 [ilist (l ++ l')] 拆回 [ilist l] 与 [ilist l'] 两半。注意递归要知道 [l]（不只是 [l ++ l']），因分裂点由 [l] 的长度决定。
*)
Equations isplit `(xs : ilist (l ++ l')) : ilist l * ilist l'  :=
  isplit (l:=[]) xs := (tt, xs);
  isplit (x, xs) with isplit xs := {
    | (xs', ys) => ((x, xs'), ys)
  }.

End ilist.

(*
 Map over an indexed list, reindexing along [f : A -> C].  Each element
 [x : B a] is sent to [k a x : D (f a)], so the whole [ilist] over [l] for
 family [B] becomes an [ilist] over [map f l] for family [D].  This is the
 functorial action of [ilist] (CPDT's [imap]). 

 --------
 沿 [f : A -> C] 重指标地映射指标列表。每个 [x : B a] 送到 [k a x : D (f a)]，故族 [B] 上关于 [l] 的整个 [ilist] 变为族 [D] 上关于 [map f l] 的 [ilist]。这是 [ilist] 的函子作用（CPDT 的 [imap]）。
*)
Equations imap `(f : A → C) `(k : ∀ (a : A), B a → D (f a))
  `(xs : @ilist A B l) : @ilist C D (map f l) :=
  imap f k (l:=[]) tt := tt;
  imap f k (l:=j :: js) (x, xs) := (k j x, imap f k xs).

(*
 The index-preserving special case of [imap]: keep the same index list [l]
 and only change the value family from [B] to [C] via [k a : B a -> C a]. 

 --------
 [imap] 的保指标特例：保持同一指标表 [l]，仅经 [k a : B a -> C a] 把值族从 [B] 换成 [C]。
*)
Equations imap' `(k : ∀ (a : A), B a → C a)
  `(xs : @ilist A B l) : @ilist A C l :=
  imap' k (l:=[]) tt := tt;
  imap' k (l:=j :: js) (x, xs) := (k j x, imap' k xs).
