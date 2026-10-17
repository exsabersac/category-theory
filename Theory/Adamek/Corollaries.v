Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Instance.Omega.
Require Import Category.Construction.Chain.
Require Import Category.Theory.Adamek.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Corollaries of Adámek's initial-algebra theorem *)

(*
 nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra


   （本文件文首说明见 nLab/Wikipedia 链接。）Judaism 绚丽远 雅丫
。 派代表参加中出现的申请羚实情。 。之间的平衡。有经验的 你先。 你干嘛 请问嬷 还好。 我感觉向秘书处提供。 。 。 。 。 。 积极支持。 。 。 ình在确定。 。 。 。 。 。 。 。为他们提供。 。 执行其。 我们正在。这一部分。 。的年龄。 。 。的职权。 。 ): 。 他是个假如 。 我没事。社会性别问题。 提供技术咨询。 。的关键要素。 我们会。 。 。抉。 齐心协力。 我不知道。  而是。 将能够。 妇女参与政治 有助于促进。 。  nào。 。 。  Collins。谭。。公民。 。 由一个。 。 鹫。 ỉ。 。 。 ada并对其。 。 。 。

列有 我真希望大家能将能与你靓的谈话列有 主席F2 0将能-F靓.

( 这就是我们  time. 91. 嘞!

   （英文长注释已压缩为中文导言；Coq 标识符未改。）
*)

(*
   [余完备 C] (Structure/完备.v) is [∀ D (G : D ⟶ C), 余极限 G].

   本节：Applying it ω-shape [Omega] diagram [Chain F] yields 余极限 [余极限 (Chain F)] that [adamek] requires, no further hypotheses. We then feed that 余极限 together supplied [AdamekData] [adamek].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary adamek_cocomplete
  {C : Category} `{@Initial C} (F : C ⟶ C)
  (CC : @Cocomplete C)
  (D : AdamekData F (CC _ (Chain F))) :
  @Initial (FAlg F).
Proof.
  exact (adamek F (CC _ (Chain F)) D).
Qed.

(*
   The option 自函子 [NatF X := option X = 1 + X] on COQ (Instance/Coq.v).

   本节说明相关定义、性质与动机。 It is polynomial 自函子 whose initial 代数 is type [nat]: structure map [1 + nat ~> nat] is [O]/[S] ([None ↦ O], [Some k ↦ S k]), initiality is exactly primitive recursion [nat].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Keep obligation handling explicit and predictable (as in Instance/Coq/Lists.v):
   surface each functor law as its own obligation rather than letting the ambient
   [cat_simpl] discharge or reshape them. *)
#[local] Obligation Tactic := idtac.

Program Definition NatF : Coq ⟶ Coq := {|
  fobj := fun X => option X;
  fmap := fun X Y (f : X -> Y) o =>
            match o with
            | None   => None
            | Some x => Some (f x)
            end
|}.
Next Obligation.
  (* fmap respects pointwise equality of functions *)
  intros X Y f g Hfg o.
  destruct o as [x|].
  - simpl; rewrite (Hfg x); reflexivity.
  - reflexivity.
Qed.
Next Obligation.
  (* fmap preserves identities *)
  intros X o.
  destruct o as [x|]; reflexivity.
Qed.
Next Obligation.
  (* fmap preserves composition *)
  intros X Y Z f g o.
  destruct o as [x|]; reflexivity.
Qed.
