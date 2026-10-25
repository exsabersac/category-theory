(*
Epi implies PROPOSITIONAL surjectivity in [Ab] and in [RMod R], and not
   the split form.

   Mac Lane's §I.7 proposition -- a homomorphism of abelian groups is epic
   exactly when it is surjective -- is proved in Instance/Ab.v by probing with
   the quotient [B/fA].  Before the PR "algebraic carriers are sets"
   (2026-09-17) the coset relation was [Type]-valued, so the preimage came
   back out as DATA and [ab_epic_surjective] concluded the split
   [AbSurjective].  The relation is now a [Prop] ([ab_coset_eq]), because
   every [AbObject] carries [cmon_prop] and a quotient's equality has to be a
   [Prop] for the field to be supplied at all.  The conclusion is therefore
   [AbPropSurjective], and the preimage is no longer data.

   Nothing is doubly negated and no choice principle is consumed: the
   existential is Coq's [ex].  What the negatives below pin is exactly the one
   thing lost -- the [Prop] existential cannot be destructed into the
   [Type]-valued [AbSurjective] -- and the controls show the two directions
   that survive: the split notion still implies the propositional one
   ([ab_surjective_prop]), and it still implies [Epic] ([ab_surjective_epic]).

   Both negatives were stripped once, in a copy of this whole file, and both
   report

     Error: Incorrect elimination in the inductive type "ex": the return type
     has sort "Type" while it should be SProp or Prop.  Elimination of an
     inductive object of sort Prop is not allowed on a predicate in sort
     "Type" because proofs can be eliminated only to build proofs.

   The import lists are the union of Instance/Ab.v's and Instance/Mod.v's.

--------
Epi 在 [Ab] 和 [RMod R] 中意味着命题上的满射，而不是分裂形式。

Mac Lane 的 §I.7 命题——阿贝尔群的同态当且仅当它是满射时才是史诗态——在 Instance/Ab.v 中通过使用商 [B/fA] 进行探测来证明。在 PR “代数载体是集合”（2026-09-17）之前，陪集关系的值为 [Type]，因此原像以 DATA 的形式返回，[ab_epic_surjective] 得出分解 [AbSurjective]。该关系现在是一个 [Prop]（[ab_coset_eq]），因为每个 [AbObject] 携带 [cmon_prop]，并且商的相等性必须是 [Prop]，才能提供该域。因此结论是 [AbPropSurjective]，并且原像不再是数据。

没有什么被双重否定，也没有选择原则被使用：存在量词是 Coq 的 [ex]。下面否定所固定的正是唯一丢失的东西——[Prop] 存在量词不能被析构为 [Type] 值的 [AbSurjective]——而控制显示了存活的两个方向：分裂概念仍然意味着命题性概念（[ab_surjective_prop]），并且它仍然意味着 [Epic]（[ab_surjective_epic]）。

两个负数在这个整个文件的副本中各自被剥离了一次，并且都报告了

错误：在归纳类型 “ex” 中消除不正确：返回类型的排序为 “Type”，而它应该是 SProp 或 Prop。不能在排序为 “Type” 的谓词上消除排序为 Prop 的归纳对象，因为证明只能用于构建其他证明。

导入列表是 Instance/Ab.v 和 Instance/Mod.v 的并集。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Preadditive.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(** ** NEGATIVE: the propositional witness is not data / ** 否定：命题见证不是数据 *)

(*
The [Prop] existential may not be destructed into the [Type]-valued
   [AbSurjective].  A [Fail Lemma] on the statement alone would be vacuous --
   [AbPropSurjective f → AbSurjective f] is a perfectly well formed type --
   so the negative carries its proof.

--------
[Prop] 存在型不能被销毁为 [Type] 值的 [AbSurjective]。仅在语句上加上 [Fail Lemma] 是没有意义的——[AbPropSurjective f → AbSurjective f] 是一个完全良构的类型——因此否定包含了它的证明。
*)
Fail Definition ab_prop_surjective_is_not_split
  {A B : AbObject} (f : A ~{Ab}~> B) (Hs : AbPropSurjective f) :
  AbSurjective f :=
  ltac:(intro b; destruct (Hs b) as [a Ha]; exists a;
        exact (pequiv_to _ _ Ha)).

(* The same for modules. / 模块也是一样。 *)
Fail Definition rmod_prop_surjective_is_not_split
  {R : RingObject} {M N : RModObject R} (f : M ~{RMod R}~> N)
  (Hs : RModPropSurjective f) : RModSurjective f :=
  ltac:(intro b; destruct (Hs b) as [a Ha]; exists a;
        exact (pequiv_to _ _ Ha)).

(** ** CONTROLS: the directions that survive / ** 控制：幸存下来的方向 *)

(*
The split notion implies the propositional one -- the direction that
   loses nothing, and the positive control for the two negatives above.

--------
分裂概念暗示命题概念——这个方向没有损失，并且是上面两个否定的积极控制。
*)
Example ab_split_implies_prop {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → AbPropSurjective f :=
  ab_surjective_prop f.

Example rmod_split_implies_prop {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModSurjective f → RModPropSurjective f :=
  rmod_surjective_prop f.

(*
Both notions still imply [Epic]; the split one directly, the
   propositional one through [pequiv_to].  The split half ([ab_split_epic])
   also compiles in the unchanged tree: it is a not-lost check, not a
   control of the change; the propositional halves cannot even be stated
   there.

--------
这两个概念仍然暗示 [Epic]；拆分的概念直接暗示，命题的概念则通过 [pequiv_to] 暗示。拆分的一半（[ab_split_epic]）在未更改的树中也能编译：它是一个非丢失检查，而不是对更改的控制；命题的一半甚至无法在那里表达。
*)
Example ab_split_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → Epic f := ab_surjective_epic f.

Example ab_prop_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbPropSurjective f → Epic f := ab_prop_surjective_epic f.

Example rmod_prop_epic {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModPropSurjective f → Epic f :=
  rmod_prop_surjective_epic f.

(* And the headline biconditionals, APPLIED, at their restated strength. / 以及标题上的双条件句，已应用，达到了它们重新陈述的强度。 *)
Example ab_epic_iff {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f ↔ AbPropSurjective f := ab_epic_iff_surjective f.

Example rmod_epic_iff_readback {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Epic f ↔ RModPropSurjective f :=
  rmod_epic_iff f.

(** ** The split notions are still there, and still say what they said / ** 分裂的观念仍然存在，仍然说它们曾经说过的话 *)

(*
A not-lost check (it holds in the unchanged tree too), not a control of
   the change.

--------
一个未丢失的检查（它在未改变的树中也成立），而不是对更改的控制。
*)
Example ab_surjective_is_sigma {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f
    = (∀ b : carrier (cmon_setoid B), { a & cmon_map f a ≈ b })
  := eq_refl.

(** ** Instrument check, scope-free / ** 仪器检查，无范围 *)

Fail Example probe_ab_prop_surjective_instrument : true = false := eq_refl.
