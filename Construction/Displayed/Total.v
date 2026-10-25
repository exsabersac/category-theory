Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.

Generalizable All Variables.

(* * * The total category of a displayed category / * * 显示类别的总类别 *)

(*
 nLab:      https://ncatlab.org/nlab/show/displayed+category
 nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
 Wikipedia: https://en.wikipedia.org/wiki/Fibred_category
 Reference: Benedikt Ahrens and Peter LeFanu Lumsdaine, "Displayed
 Categories", Logical Methods in Computer Science 15(1), 2019.
 https://arxiv.org/abs/1705.04296

 The total category ∫ D of a displayed category D over C: objects are
 dependent pairs (x; dx) of a base object x : C and an object dx displayed
 over it; morphisms (x; dx) ~> (y; dy) are dependent pairs (f; ff) of a
 base morphism f : x ~> y and a displayed morphism ff : dhom dx dy f lying
 over it. Since base morphisms are compared by ≈ rather than by equality,
 two total morphisms are equivalent when some proof e relates their base
 components and transporting the first displayed component along e yields
 the second; by proof irrelevance of transport ([dtransport_id], and its
 consequence [dtransport_proof_irrel]) the choice of e is immaterial, so
 this is a bona fide equivalence relation.

 Identity and composition are the displayed ones paired over the base
 ones. Each category law is proven by supplying the base law as the first
 component and closing the displayed side with the derived transport
 lemma pack of Theory/Displayed.v ([dtransport_did_left],
 [dtransport_did_right], [dtransport_dcomp_assoc], and friends), which was
 budgeted there for exactly this purpose.

 [Total_Proj] is the evident projection functor ∫ D ⟶ C taking first
 components; its functor laws hold by reflexivity because identity and
 composition in ∫ D are componentwise. Cleavings on D make this projection
 a cloven fibration — see Theory/Fibration.v. 

 --------
 nLab:       https://ncatlab.org/nlab/show/displayed+category 
 nLab:       https://ncatlab.org/nlab/show/Grothendieck+construction 
 维基百科:  https://en.wikipedia.org/wiki/Fibred_category 
 参考文献: Benedikt Ahrens 和 Peter LeFanu Lumsdaine, “Displayed Categories”, 《计算机科学中的逻辑方法》 15(1), 2019. https://arxiv.org/abs/1705.04296一个展示范畴 D 在 C 上的总范畴 ∫ D：对象是底范畴对象 x : C 和其上展示的对象 dx 的依赖对 (x; dx)；态射 (x; dx) ~> (y; dy) 是底态射 f : x ~> y 和位于其上的展示态射 ff : dhom dx dy f 的依赖对 (f; ff)。由于底态射是通过 ≈ 而不是通过等式来比较的，当某个证明 e 将它们的底组件联系起来，并且沿着 e 将第一个展示组件传送得到第二个时，两个总态射被认为是等价的；根据传送的证明无关性（[dtransport_id] 及其结果 [dtransport_proof_irrel]），e 的选择无关紧要，因此这是一个真正的等价关系。身份和组合是显示的部分与基部分配对的。每个范畴定律都通过提供基定律作为第一个组件，并使用 Theory/Displayed.v 中的派生传输引理包（[dtransport_did_left]、[dtransport_did_right]、[dtransport_dcomp_assoc] 及其相关内容）闭合显示侧来证明，这正是该处专门为此目的安排的。

 [Total_Proj] 是显而易见的投影函子 ∫ D ⟶ C，取第一个组件；由于 ∫ D 中的身份和组合是逐组件的，它的函子定律通过自反性成立。D 上的劈分使该投影成为一个分裂纤维——参见 Theory/Fibration.v。
*)

#[local] Obligation Tactic := program_simpl.

Program Definition Total {C : Category} (D : Displayed C) : Category := {|
  obj := ∃ x : C, dobj x;
  hom := fun x y => ∃ f : `1 x ~> `1 y, dhom (`2 x) (`2 y) f;
  homset := fun x y => {| equiv := fun f g =>
    { e : `1 f ≈ `1 g & dtransport e (`2 f) ≈ `2 g } |};
  id := fun x => (id; did (`2 x));
  compose := fun x y z f g => (`1 f ∘ `1 g; dcomp (`2 f) (`2 g))
|}.
Next Obligation.
  (* The total hom equivalence is an equivalence relation. / 总同构等价是一个等价关系。 *)
  split.
  - (* reflexivity: the identity proof, cancelled by [dtransport_id] / 自反性：身份证明，被 [dtransport_id] 取消 *)
    intros [f ff].
    exists (Equivalence_Reflexive f).
    now apply dtransport_id.
  - (* symmetry: invert the base proof; flip the transport across ≈ / 对称性：取基本证明的逆；翻转跨 ≈ 的传输 *)
    intros [f ff] [g gg] [e He]; simpl in *.
    exists (symmetry e).
    symmetry.
    now apply (fst (dtransport_flip e ff gg)).
  - (* transitivity: compose the base proofs; fuse the transports / 传递性：组合基础证明；融合传输 *)
    intros [f ff] [g gg] [h hh] [e1 He1] [e2 He2]; simpl in *.
    exists (Equivalence_Transitive _ _ _ e1 e2).
    rewrite <- dtransport_trans.
    now rewrite He1.
Qed.
Next Obligation.
  (* Composition respects the total equivalence in both arguments. / 组合在两个论点中都尊重完全等价。 *)
  intros [f1 ff1] [g1 gg1] [e1 He1] [f2 ff2] [g2 gg2] [e2 He2]; simpl in *.
  exists (compose_respects _ _ e1 _ _ e2).
  rewrite <- He1, <- He2.
  symmetry.
  apply dtransport_dcomp.
Qed.
Next Obligation.
  (* Left identity over the base law. / 基于基础法的左恒等式。 *)
  exists (id_left _).
  apply dtransport_did_left.
Qed.
Next Obligation.
  (* Right identity over the base law. / 正确身份凌驾于基本法律之上。 *)
  exists (id_right _).
  apply dtransport_did_right.
Qed.
Next Obligation.
  (* Associativity over the base law. / 基律上的结合性。 *)
  exists (comp_assoc _ _ _).
  apply dtransport_dcomp_assoc.
Qed.
Next Obligation.
  (* Associativity, dual orientation, over the base law. / 结合性、双重方向、基础定律之上。 *)
  exists (comp_assoc_sym _ _ _).
  apply dtransport_dcomp_assoc_sym.
Qed.

(*
   * The projection functor ∫ D ⟶ C: first components. Identity and
   composition in the total category are componentwise, so both functor
   laws are the base category's, holding by reflexivity. 

   --------
   * 投影函子 ∫ D ⟶ C：取第一分量。总范畴中的恒等和复合是按分量进行的，所以两个函子律都是基范畴的，通过自反性成立。
*)

Program Definition Total_Proj {C : Category} (D : Displayed C) :
  Total D ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun x y f => `1 f
|}.
Next Obligation.
  (*
 fmap respects ≈: the base component of a total ≈ is exactly a base ≈ 

 --------
 fmap 遵守 ≈：一个总 ≈ 的基础组件恰好是一个基础 ≈
*)
  intros f g [e _]; exact e.
Qed.
Next Obligation.
  (* identities project to identities, on the nose / 身份映射到身份，恰到好处 *)
  reflexivity.
Qed.
Next Obligation.
  (* composites project to composites, on the nose / 从复合材料项目到复合材料，正中目标 *)
  reflexivity.
Qed.
