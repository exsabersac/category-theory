Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Instance.Coq.
Require Import List.

Generalizable All Variables.

(* * * Lists as the initial algebra of the list endofunctor over COQ / * * 列表作为 COQ 上列表自函子的初代数 *)

(*
 nLab:      https://ncatlab.org/nlab/show/inductive+type
 Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

 The polynomial endofunctor [ListF A X := 1 + A × X] on COQ (Instance/Coq.v)
 has the type [list A] as its initial algebra.  The structure map
 [alg : 1 + A × list A ~> list A] is [nil]/[cons], and initiality is exactly
 the recursion principle of lists: for every [ListF A]-algebra
 [β : 1 + A × Y ~> Y] there is a unique algebra map [list A ~> Y], namely the
 fold (a [foldr]-style catamorphism) determined by [β].  Uniqueness is the
 list induction that any algebra map into [(Y, β)] agrees with the fold.

 This exhibits [list A] as the least fixed point [μ (ListF A)]; by Lambek's
 lemma (Theory/Lambek.v) the structure map is then an isomorphism
 [1 + A × list A ≅ list A].  The whole development stays within pointwise
 equality on COQ hom-sets and ordinary list induction, so it carries no
 axioms (in particular no functional extensionality). 

 --------
 nLab：https://ncatlab.org/nlab/show/inductive+type
 维基百科：https://en.wikipedia.org/wiki/Initial_algebra

 在 COQ（Instance/Coq.v）上的多项式自函子 [ListF A X := 1 + A × X] 的初代数类型为 [list A]。结构映射 [alg : 1 + A × list A ~> list A] 是 [nil] / [cons]，初始性恰好就是列表的递归原理：对于每一个 [ListF A]-代数 [β : 1 + A × Y ~> Y]，存在唯一的代数映射 [list A ~> Y]，即由 [β] 确定的 fold（一种 [foldr] 风格的カタモルフィズム）。唯一性是列表归纳法，任何映射到 [(Y, β)] 的代数映射都与 fold 一致。这展示了 [list A] 作为最小不动点 [μ (ListF A)]；根据 Lambek 引理（Theory/Lambek.v），结构映射随后就是一个同构 [1 + A × list A ≅ list A]。整个发展保持在 COQ 同态集的逐点相等性和普通的列表归纳法之内，因此它不依赖任何公理（特别是不依赖函数外延性）。
*)

(*
 Keep obligation handling explicit and predictable: the file builds functor
 and F-algebra-hom records whose remaining fields are commuting squares, and
 we want every one surfaced as its own obligation rather than silently
 discharged. 

 --------
 保持义务处理明确且可预测：该文件构建了函子和F-代数同态记录，其剩余字段是交换方格，我们希望每一个都以其自己的义务显示出来，而不是被静默解除。
*)
#[local] Obligation Tactic := idtac.

(* The list endofunctor [ListF A X = option (A * X) = 1 + A × X]. / 列表端函子 [ListF A X = option (A * X) = 1 + A × X]。 *)
Program Definition ListF (A : Type) : Coq ⟶ Coq := {|
  fobj := fun X => option (A * X)%type;
  fmap := fun X Y (f : X -> Y) o =>
            match o with
            | None => None
            | Some (a, x) => Some (a, f x)
            end
|}.
Next Obligation.
  (* fmap respects pointwise equality / fmap 尊重逐点相等 *)
  intros A X Y f g Hfg o.
  destruct o as [[a x]|].
  - simpl; rewrite (Hfg x); reflexivity.
  - reflexivity.
Qed.
Next Obligation.
  (* fmap preserves identities / fmap 保持恒等式 *)
  intros A X o.
  destruct o as [[a x]|]; reflexivity.
Qed.
Next Obligation.
  (* fmap preserves composition / fmap 保持组合性 *)
  intros A X Y Z f g o.
  destruct o as [[a x]|]; reflexivity.
Qed.

(* The structure map of the list algebra: [None] is [nil] and [Some (a, l)] is [cons a l]. This is a [ListF A]-algebra on [list A]. / 列表代数的结构图：[None] 是 [nil]，[Some (a, l)] 是 [cons a l]。这是 [ListF A] 上的 [list A] 代数。 *)
Definition alg (A : Type) : ListF A (list A) ~{Coq}~> list A :=
  fun o => match o with
           | None => @nil A
           | Some (a, l) => cons a l
           end.

(* The catamorphism (fold) determined by an algebra [β : 1 + A × Y ~> Y]. This is the carrier of the unique algebra map out of [(list A, alg A)]. / 由代数 [β : 1 + A × Y ~> Y] 决定的双模态同态（fold）。这是从 [(list A, alg A)] 唯一代数映射的承载对象。 *)
Fixpoint fold {A Y : Type} (beta : option (A * Y)%type -> Y)
              (l : list A) : Y :=
  match l with
  | nil => beta None
  | cons a l' => beta (Some (a, fold beta l'))
  end.

(*
 Any [ListF A]-algebra map [h : (list A, alg A) ~> (Y, β)] coincides with the
 fold determined by [β].  This is the uniqueness half of initiality, proven by
 induction on the list using the commuting-square hypothesis [Hh] at the two
 relevant argument shapes. 

 --------
 任何 [ListF A]-代数映射 [h : (list A, alg A) ~> (Y, β)] 都与 [β] 确定的 fold 一致。这是初始性的一半唯一性，通过对列表进行归纳证明，使用在两个相关参数形状下的交换方格假设 [Hh]。
*)
Lemma hom_is_fold {A Y : Type} (beta : option (A * Y)%type -> Y)
      (h : list A -> Y)
      (Hh : forall o, h (alg A o) = beta (fmap[ListF A] h o))
      (l : list A) : h l = fold beta l.
Proof.
  induction l as [|a l' IH].
  - apply (Hh None).
  - simpl.
    rewrite <- IH.
    apply (Hh (Some (a, l'))).
Qed.

(*
 The unique algebra map from [(list A, alg A)] to an arbitrary algebra [y],
 packaging the fold together with its commuting square. 

 --------
 从  [(list A, alg A)]  到任意代数  [y] 的唯一代数映射，将折叠及其交换方一起打包。
*)
Program Definition list_alg_hom (A : Type) (y : FAlg (ListF A))
  : (list A; alg A) ~{FAlg (ListF A)}~> y :=
  {| falg_hom := fold (`2 y) |}.
Next Obligation.
  (* fold ∘ alg ≈ β ∘ fmap fold, checked shape by shape / fold ∘ alg ≈ β ∘ fmap fold，逐个形状检查 *)
  intros A y o.
  destruct o as [[a l]|]; reflexivity.
Qed.

(*
 [list A] together with [alg A] is the initial [ListF A]-algebra: it is the
 terminal object of the opposite of the algebra category. 

 --------
 [list A] 连同 [alg A] 是初始的 [ListF A] -代数：它是代数范畴的对偶范畴中的终对象。
*)
Program Definition list_initial (A : Type) : @Initial (FAlg (ListF A)) := {|
  terminal_obj := (list A; alg A);
  one := fun y => list_alg_hom A y
|}.
Next Obligation.
  (* uniqueness: any two algebra maps out of [(list A, alg A)] agree, since each coincides with the fold determined by the target algebra / 唯一性：从 [(list A, alg A)] 出发的任意两个代数映射都一致，因为每个映射都与目标代数确定的折叠相符 *)
  intros A x f g.
  destruct f as [hf Hf], g as [hg Hg].
  intro l; simpl.
  rewrite (hom_is_fold (`2 x) hf Hf l).
  rewrite (hom_is_fold (`2 x) hg Hg l).
  reflexivity.
Qed.
