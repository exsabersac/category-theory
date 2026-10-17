From Coq Require Import Lia.
Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PreorderReflection.

Generalizable All Variables.

(** * 图与交换性 *)

(* nLab: https://ncatlab.org/nlab/show/commutative+diagram

   范畴 [C] 中形状为 quiver [G] 的图 (diagram)：顶点映到对象，边映到端点标签之间的态射。
   交换性说：沿任意两路径的复合在 ≈ 下一致。本文件给出图的数据与交换条件；与极限/余极限
   的连接见 Structure/Limit 与相关构造。长历史短文若仍为英文属后续波次。 *)

(*
   图和折算:来源和树间联系

书:麦克莱恩, 我只是"工作数学小镇的范畴",第2 你说什么?业经我一下导则了?
S 你不觉得ỡter GTM 5, 1998,建议将第I.1节,“为实现范畴玲就这些目的芷 你不会应酌情认为, 我还认为,“为了达到这一目的,让你们”
(PD của第18页)阎该节 đó的第三个编号定义.
下辖以下地区:蟑螂社区(F. S.
上帝的旨意 §3.3.4匀定义3.51这些文件已印编撰第95页 (PDF第107页 我是 我已经写了"所订的"定义"是联合国的抉择载于本报告附件一)
嘘k: R
第后代权利对现有行使为实现《公约
之之之昼之之向秘书处提交之之以之之之以之之以之以之之以之之以之之以之以之是否会之以之以 nào之 我以为你之体现在之以之以之 你是不是以
盏:Z提出的申诉虫

未被   庵 我爱 可利用 将按照和仍在进行和 和隧和和和 晚安全面地和和

   （原英文长文首已压缩为中文导言；标识符未改。）
*)

#[local] Existing Instance edgeset.

(* 相关说明。 （已译） *)

Section DiagramCore.

Context {G : Quiver}.
Context {C : Category}.

(* A diagram [C] shape [G]: vertices go 对象, edges 态射
 between labels their endpoints. Source target preservation is
 automatic because [Quiver]'s edges are indexed their endpoints.（已译） *)
Definition Diagram : Type := QuiverHomomorphism G (QuiverOfCat C).

Context (D : Diagram).

(* The 态射 labelling edge. [fnodes] coercion, so [D x] the
 对象 labelling vertex [x]. （已译） *)
Definition dedge {x y : G} (e : edges x y) : D x ~{C}~> D y :=
  @fedgemap G (QuiverOfCat C) D x y e.

(*后后后后后创造有利于拥护后ô加大力度淌后后 页 、-
được 表示身份;已为喽啰嘞的Z语。
提供咨询意见, * 因为一个路径运行源审查报告目标, 而享有同等权利 。*)
Fixpoint dpath {x y : G} (p : tlist edges x y) : D x ~{C}~> D y :=
  match p in tlist' _ i return D i ~{C}~> D y with
  | tnil            => id
  | tcons _ e rest  => dpath rest ∘ dedge e
  end.

(* Path denotation turns concatenation into composition. *)
Lemma dpath_app {x y z : G} (p : tlist edges x y) (q : tlist edges y z) :
  dpath (p +++ q) ≈ dpath q ∘ dpath p.
Proof.
  induction p as [ | i m e p IH ].
  - rewrite tlist_app_tnil_l; simpl.
    now rewrite id_right.
  - rewrite <- tlist_app_comm_cons; simpl.
    rewrite IH.
    now rewrite comp_assoc.
Qed.

(*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Commutative : Type :=
  ∀ (x y : G) (p q : tlist edges x y), dpath p ≈ dpath q.

End DiagramCore.

Arguments Diagram : clear implicits.
Arguments dedge {G C} D {x y} e.
Arguments dpath {G C} D {x y} p.
Arguments Commutative {G C} D.

(* * ** The diagram-as-函子 form predicate （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CommutativeShape {J C : Category} (F : J ⟶ C) : Type :=
  ∀ (x y : J) (f g : x ~{J}~> y), fmap[F] f ≈ fmap[F] g.

(* * ** The bridge free 范畴 （已译） *)

Section DiagramBridge.

Context {G : Quiver}.
Context {C : Category}.

(* A diagram extends 函子 free 范畴: 这是 Quiver.v's
 [InducedFunctor], named here correspondence. （已译） *)
Definition FunctorOfDiagram (D : Diagram G C) : FreeOnQuiver G ⟶ C :=
  InducedFunctor G D.

(* ... 函子 free 范畴 restricts diagram, by
 composing unit free/forgetful 伴随, sends an
 edge one-edge path. （已译） *)
Definition DiagramOfFunctor (F : FreeOnQuiver G ⟶ C) : Diagram G C :=
  QuiverComp (UnitQuiverCatAdjunction G)
             (QuiverHomomorphismOfFunctor (FreeOnQuiver G) C F).

(* Path denotation is the extending functor's action on morphisms. *)
Lemma dpath_fmap (D : Diagram G C) {x y : G} (p : tlist edges x y) :
  dpath D p ≈ fmap[FunctorOfDiagram D] p.
Proof.
  induction p as [ | i m e p IH ]; simpl; [ reflexivity | ].
  now rewrite IH.
Qed.

(* Denoting path restricted diagram applying original 函子
 path, viewed 态射 free 范畴. Proved paths
 arbitrary length, induction. （已译） *)
Lemma dpath_of_functor (F : FreeOnQuiver G ⟶ C) {x y : G} (p : tlist edges x y) :
  dpath (DiagramOfFunctor F) p ≈ fmap[F] p.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - change (@tnil _ _ y) with (@id (FreeOnQuiver G) y).
    now rewrite fmap_id.
  - (*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    assert (Hsplit : @equiv _ (@homset (FreeOnQuiver G) i y) (e ::: p)
                       (@compose (FreeOnQuiver G) _ _ _ p (tlist_singleton e)))
      by (unfold tlist_singleton; simpl; now rewrite <- tlist_app_cons).
    rewrite Hsplit, fmap_comp.
    apply compose_respects; [ exact IH | reflexivity ].
Qed.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma functor_of_diagram_of_functor (F : FreeOnQuiver G ⟶ C) :
  @equiv _ (@Functor_StrictEq_Setoid (FreeOnQuiver G) C)
         (FunctorOfDiagram (DiagramOfFunctor F)) F.
Proof.
  exists (fun _ => eq_refl).
  intros x y p.
  change (fmap[FunctorOfDiagram (DiagramOfFunctor F)] p ≈ fmap[F] p).
  transitivity (dpath (DiagramOfFunctor F) p);
    [ symmetry; apply dpath_fmap | apply dpath_of_functor ].
Qed.

(*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma diagram_of_functor_of_diagram (D : Diagram G C) :
  DiagramOfFunctor (FunctorOfDiagram D) ≈[QuiverCategory] D.
Proof.
  exists (fun _ => eq_refl).
  intros x y e; simpl.
  now rewrite id_left.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem commutative_iff_shape (D : Diagram G C) :
  Commutative D ↔ CommutativeShape (FunctorOfDiagram D).
Proof.
  split; intros H x y p q.
  - transitivity (dpath D p); [ symmetry; apply dpath_fmap | ].
    transitivity (dpath D q); [ apply H | apply dpath_fmap ].
  - transitivity (fmap[FunctorOfDiagram D] p); [ apply dpath_fmap | ].
    transitivity (fmap[FunctorOfDiagram D] q);
      [ apply H | symmetry; apply dpath_fmap ].
Qed.

(* The same correspondence read 函子 side. （已译） *)
Theorem shape_iff_commutative (F : FreeOnQuiver G ⟶ C) :
  CommutativeShape F ↔ Commutative (DiagramOfFunctor F).
Proof.
  split; intros H x y p q.
  - transitivity (fmap[F] p); [ apply dpath_of_functor | ].
    transitivity (fmap[F] q); [ apply H | symmetry; apply dpath_of_functor ].
  - transitivity (dpath (DiagramOfFunctor F) p);
      [ symmetry; apply dpath_of_functor | ].
    transitivity (dpath (DiagramOfFunctor F) q);
      [ apply H | apply dpath_of_functor ].
Qed.

End DiagramBridge.

(** ** Terms over a diagram *)

Section DiagramTerms.

Context {G : Quiver}.
Context {C : Category}.
Context (D : Diagram G C).

(* Interpret formal 复合 (Construction/Free/Quiver.v) [C]. The
 reading [Comp f g] [f ∘ g] one Solver/Denote.v documents for
 untyped [Term] Solver/Expr.v. （已译） *)
Fixpoint dterm {x y : G} (t : Mor x y) : D x ~{C}~> D y :=
  match t in @Mor _ x0 y0 return D x0 ~{C}~> D y0 with
  | Ident      => id
  | Morph e    => dedge D e
  | Comp f g   => dterm f ∘ dterm g
  end.

(* 相关说明。 （已译） *)
Lemma dterm_dpath {x y : G} (t : Mor x y) : dterm t ≈ dpath D (morDA t).
Proof.
  induction t as [ x | x y e | x y z f IHf g IHg ]; simpl.
  - reflexivity.
  - now rewrite id_left.
  - rewrite dpath_app.
    now rewrite IHf, IHg.
Qed.

(* Over a commutative diagram every pair of parallel terms is interchangeable,
   whatever their shapes or lengths. *)
Corollary commutative_dterm (Hc : Commutative D) {x y : G} (s t : Mor x y) :
  dterm s ≈ dterm t.
Proof.
  rewrite (dterm_dpath s), (dterm_dpath t).
  now apply Hc.
Qed.

End DiagramTerms.

Arguments dterm {G C} D {x y} t.

(* * ** Transporting diagram along 函子 （已译） *)

Section DiagramFunctorial.

Context {G : Quiver}.
Context {C E : Category}.

(* The image of a diagram under a functor, again a diagram. *)
Definition PostcomposeDiagram (U : C ⟶ E) (D : Diagram G C) : Diagram G E :=
  QuiverComp D (QuiverHomomorphismOfFunctor C E U).

(* The 函子 commutes path denotation, paths arbitrary length. （已译） *)
Lemma dpath_postcompose (U : C ⟶ E) (D : Diagram G C)
      {x y : G} (p : tlist edges x y) :
  dpath (PostcomposeDiagram U D) p ≈ fmap[U] (dpath D p).
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - now rewrite fmap_id.
  - transitivity (fmap[U] (dpath D p) ∘ fmap[U] (dedge D e)).
    + apply compose_respects; [ exact IH | reflexivity ].
    + symmetry; apply fmap_comp.
Qed.

(* Every functor preserves commutativity. *)
Theorem functor_preserves_commutative (U : C ⟶ E) (D : Diagram G C) :
  Commutative D -> Commutative (PostcomposeDiagram U D).
Proof.
  intros Hc x y p q.
  transitivity (fmap[U] (dpath D p)); [ apply dpath_postcompose | ].
  transitivity (fmap[U] (dpath D q));
    [ apply fmap_respects, Hc | symmetry; apply dpath_postcompose ].
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem faithful_reflects_commutative (U : C ⟶ E) `{@Faithful C E U}
        (D : Diagram G C) :
  Commutative (PostcomposeDiagram U D) -> Commutative D.
Proof.
  intros Hc x y p q.
  apply fmap_inj.
  transitivity (dpath (PostcomposeDiagram U D) p);
    [ symmetry; apply dpath_postcompose | ].
  transitivity (dpath (PostcomposeDiagram U D) q);
    [ apply Hc | apply dpath_postcompose ].
Qed.

End DiagramFunctorial.

(* The same two facts diagram-as-函子 formulation, where they need
 no quiver at all: they hold diagram indexed ANY 范畴. （已译） *)
Theorem functor_preserves_commutative_shape {J C E : Category}
        (U : C ⟶ E) (F : J ⟶ C) :
  CommutativeShape F -> CommutativeShape (U ◯ F).
Proof.
  intros Hc x y f g; simpl.
  now apply fmap_respects, Hc.
Qed.

Theorem faithful_reflects_commutative_shape {J C E : Category}
        (U : C ⟶ E) `{@Faithful C E U} (F : J ⟶ C) :
  CommutativeShape (U ◯ F) -> CommutativeShape F.
Proof.
  intros Hc x y f g.
  apply fmap_inj.
  exact (Hc x y f g).
Qed.

(** ** The walking square *)

(* 相关说明。 （已译） *)
Inductive SqNode : Set := SqA | SqB | SqC | SqD.

Definition sq_edge (i j : SqNode) : Type :=
  match i, j with
  | SqA, SqB => unit
  | SqA, SqC => unit
  | SqB, SqD => unit
  | SqC, SqD => unit
  | _  , _   => Empty_set
  end.

Definition SquareQuiver : Quiver := Build_Quiver_Standard_Eq SqNode sq_edge.

(* 相关说明。 （已译） *)
Example sq_edge_AB : @edges SquareQuiver SqA SqB = unit := eq_refl.
Example sq_edge_BD : @edges SquareQuiver SqB SqD = unit := eq_refl.
Example sq_edge_DA : @edges SquareQuiver SqD SqA = Empty_set := eq_refl.

(* The two paths from A to D. *)
Definition sq_via_B : tlist (@edges SquareQuiver) SqA SqD :=
  tcons SqA (tt : @edges SquareQuiver SqA SqB)
    (tcons SqB (tt : @edges SquareQuiver SqB SqD) tnil).

Definition sq_via_C : tlist (@edges SquareQuiver) SqA SqD :=
  tcons SqA (tt : @edges SquareQuiver SqA SqC)
    (tcons SqC (tt : @edges SquareQuiver SqC SqD) tnil).

(*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sq_via_B_neq_via_C :
  (sq_via_B ≈[FreeOnQuiver SquareQuiver] sq_via_C) -> False.
Proof.
  intro Hbc.
  unfold sq_via_B, sq_via_C in Hbc; simpl in Hbc.
  destruct Hbc as [Hq _ _].
  discriminate Hq.
Qed.

(*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sq_rank (i : SqNode) : nat :=
  match i with SqA => 0 | SqB => 1 | SqC => 1 | SqD => 2 end.

Lemma sq_len_rank (i j : SqNode) (p : tlist (@edges SquareQuiver) i j) :
  (sq_rank i + tlist_length p <= sq_rank j)%nat.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - lia.
  - destruct i, m; simpl in e; try contradiction; simpl in *; lia.
Qed.

Lemma sq_endo_paths_are_nil (i : SqNode)
      (p : tlist (@edges SquareQuiver) i i) : tlist_length p = 0%nat.
Proof. pose proof (sq_len_rank i i p); lia. Qed.

Section WalkingSquare.

Context {C : Category}.
Context {a b c d : C} (u : a ~> b) (v : b ~> d) (h : a ~> c) (k : c ~> d).

Definition sq_obj (i : SqNode) : C :=
  match i with SqA => a | SqB => b | SqC => c | SqD => d end.

Definition sq_edgemap (i j : SqNode) : sq_edge i j -> sq_obj i ~> sq_obj j :=
  match i, j return sq_edge i j -> sq_obj i ~> sq_obj j with
  | SqA, SqB => fun _ => u
  | SqA, SqC => fun _ => h
  | SqB, SqD => fun _ => v
  | SqC, SqD => fun _ => k
  | _  , _   => fun e => match e with end
  end.

Program Definition SquareDiagram : Diagram SquareQuiver C :=
  {| fnodes := sq_obj ; fedgemap := sq_edgemap |}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example sq_label_u : dedge SquareDiagram (tt : @edges SquareQuiver SqA SqB) = u
  := eq_refl.
Example sq_label_k : dedge SquareDiagram (tt : @edges SquareQuiver SqC SqD) = k
  := eq_refl.

(* The 复合 denoted each two paths. （已译） *)
Example sq_denote_via_B : dpath SquareDiagram sq_via_B ≈ v ∘ u.
Proof. simpl; now rewrite id_left. Qed.

Example sq_denote_via_C : dpath SquareDiagram sq_via_C ≈ k ∘ h.
Proof. simpl; now rewrite id_left. Qed.

(*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sq_spec (i j : SqNode) : (sq_obj i ~{C}~> sq_obj j) -> Type :=
  match i, j return (sq_obj i ~{C}~> sq_obj j) -> Type with
  | SqA, SqA => fun f => f ≈ id
  | SqB, SqB => fun f => f ≈ id
  | SqC, SqC => fun f => f ≈ id
  | SqD, SqD => fun f => f ≈ id
  | SqA, SqB => fun f => f ≈ u
  | SqA, SqC => fun f => f ≈ h
  | SqA, SqD => fun f => f ≈ v ∘ u
  | SqB, SqD => fun f => f ≈ v
  | SqC, SqD => fun f => f ≈ k
  | _  , _   => fun _ => False
  end.

Lemma sq_paths (Hsq : v ∘ u ≈ k ∘ h) (i j : SqNode)
      (p : tlist (@edges SquareQuiver) i j) :
  sq_spec i j (dpath SquareDiagram p).
Proof.
  induction p as [ | i m e p IH ].
  - destruct j; simpl; reflexivity.
  - (*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    destruct i, m; simpl in e; try destruct e;
      destruct j; simpl in *; try contradiction;
      rewrite IH; rewrite ?id_left; try reflexivity; [> symmetry; exact Hsq ].
Qed.

(* 相关说明。 （已译） *)
Theorem square_commutes (Hsq : v ∘ u ≈ k ∘ h) : Commutative SquareDiagram.
Proof.
  intros x y p q.
  pose proof (sq_paths Hsq _ _ p) as Hp.
  pose proof (sq_paths Hsq _ _ q) as Hq.
  destruct x, y; simpl in Hp, Hq; try contradiction;
    now rewrite Hp, Hq.
Qed.

(* 相关说明。 （已译） *)
Theorem square_commutes_inv : Commutative SquareDiagram -> v ∘ u ≈ k ∘ h.
Proof.
  intro Hc.
  pose proof (Hc SqA SqD sq_via_B sq_via_C) as Heq.
  unfold sq_via_B, sq_via_C in Heq; simpl in Heq.
  now rewrite !id_left in Heq.
Qed.

(*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem square_commutative_iff :
  Commutative SquareDiagram ↔ v ∘ u ≈ k ∘ h.
Proof.
  split; [ apply square_commutes_inv | apply square_commutes ].
Qed.

End WalkingSquare.

(** ** The walking triangle *)

(*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive TriNode : Set := TrX | TrY | TrZ.

Definition tri_edge (i j : TriNode) : Type :=
  match i, j with
  | TrX, TrY => unit
  | TrY, TrZ => unit
  | TrX, TrZ => unit
  | _  , _   => Empty_set
  end.

Definition TriangleQuiver : Quiver := Build_Quiver_Standard_Eq TriNode tri_edge.

Definition tri_via_Y : tlist (@edges TriangleQuiver) TrX TrZ :=
  tcons TrX (tt : @edges TriangleQuiver TrX TrY)
    (tcons TrY (tt : @edges TriangleQuiver TrY TrZ) tnil).

Definition tri_direct : tlist (@edges TriangleQuiver) TrX TrZ :=
  tcons TrX (tt : @edges TriangleQuiver TrX TrZ) tnil.

(*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tri_via_Y_neq_direct :
  (tri_via_Y ≈[FreeOnQuiver TriangleQuiver] tri_direct) -> False.
Proof.
  intro Hxy.
  unfold tri_via_Y, tri_direct in Hxy; simpl in Hxy.
  destruct Hxy as [Hq _ _].
  discriminate Hq.
Qed.

(* Acyclicity triangle, same rank 论元. （已译） *)
Definition tri_rank (i : TriNode) : nat :=
  match i with TrX => 0 | TrY => 1 | TrZ => 2 end.

Lemma tri_len_rank (i j : TriNode) (p : tlist (@edges TriangleQuiver) i j) :
  (tri_rank i + tlist_length p <= tri_rank j)%nat.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - lia.
  - destruct i, m; simpl in e; try contradiction; simpl in *; lia.
Qed.

Lemma tri_endo_paths_are_nil (i : TriNode)
      (p : tlist (@edges TriangleQuiver) i i) : tlist_length p = 0%nat.
Proof. pose proof (tri_len_rank i i p); lia. Qed.

Section WalkingTriangle.

Context {C : Category}.
Context {x y z : C} (u : x ~> y) (v : y ~> z) (w : x ~> z).

Definition tri_obj (i : TriNode) : C :=
  match i with TrX => x | TrY => y | TrZ => z end.

Definition tri_edgemap (i j : TriNode) : tri_edge i j -> tri_obj i ~> tri_obj j :=
  match i, j return tri_edge i j -> tri_obj i ~> tri_obj j with
  | TrX, TrY => fun _ => u
  | TrY, TrZ => fun _ => v
  | TrX, TrZ => fun _ => w
  | _  , _   => fun e => match e with end
  end.

Program Definition TriangleDiagram : Diagram TriangleQuiver C :=
  {| fnodes := tri_obj ; fedgemap := tri_edgemap |}.

Definition tri_spec (i j : TriNode) : (tri_obj i ~{C}~> tri_obj j) -> Type :=
  match i, j return (tri_obj i ~{C}~> tri_obj j) -> Type with
  | TrX, TrX => fun f => f ≈ id
  | TrY, TrY => fun f => f ≈ id
  | TrZ, TrZ => fun f => f ≈ id
  | TrX, TrY => fun f => f ≈ u
  | TrY, TrZ => fun f => f ≈ v
  | TrX, TrZ => fun f => f ≈ w
  | _  , _   => fun _ => False
  end.

Lemma tri_paths (Htri : v ∘ u ≈ w) (i j : TriNode)
      (p : tlist (@edges TriangleQuiver) i j) :
  tri_spec i j (dpath TriangleDiagram p).
Proof.
  induction p as [ | i m e p IH ].
  - destruct j; simpl; reflexivity.
  - destruct i, m; simpl in e; try destruct e;
      destruct j; simpl in *; try contradiction;
      rewrite IH; rewrite ?id_left; try reflexivity; [> exact Htri ].
Qed.

Theorem triangle_commutes (Htri : v ∘ u ≈ w) : Commutative TriangleDiagram.
Proof.
  intros i j p q.
  pose proof (tri_paths Htri _ _ p) as Hp.
  pose proof (tri_paths Htri _ _ q) as Hq.
  destruct i, j; simpl in Hp, Hq; try contradiction;
    now rewrite Hp, Hq.
Qed.

Theorem triangle_commutes_inv : Commutative TriangleDiagram -> v ∘ u ≈ w.
Proof.
  intro Hc.
  pose proof (Hc TrX TrZ tri_via_Y tri_direct) as Heq.
  unfold tri_via_Y, tri_direct in Heq; simpl in Heq.
  now rewrite !id_left in Heq.
Qed.

Theorem triangle_commutative_iff :
  Commutative TriangleDiagram ↔ v ∘ u ≈ w.
Proof.
  split; [ apply triangle_commutes_inv | apply triangle_commutes ].
Qed.

End WalkingTriangle.

(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive LoopNode : Set := LpX.

Definition loop_edge (i j : LoopNode) : Type :=
  match i, j with LpX, LpX => unit end.

Definition LoopQuiver : Quiver := Build_Quiver_Standard_Eq LoopNode loop_edge.

Example loop_edge_XX : @edges LoopQuiver LpX LpX = unit := eq_refl.

Section WalkingLoop.

Context {C : Category}.
Context {a : C}.
Context (e : a ~> a).

Definition loop_obj (i : LoopNode) : C := a.

Definition loop_edgemap (i j : LoopNode)
  : loop_edge i j -> loop_obj i ~> loop_obj j :=
  match i, j with LpX, LpX => fun _ => e end.

(*
   本节说明 Diagram 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition LoopDiagram : Diagram LoopQuiver C :=
  {| fnodes := loop_obj ; fedgemap := loop_edgemap |}.

(* Every path in this shape denotes an iterate of [e]; under [e ≈ id] they all
   denote [id]. *)
Lemma loop_paths (He : e ≈ id) (i j : LoopNode)
      (p : tlist (@edges LoopQuiver) i j) :
  dpath LoopDiagram p ≈ id.
Proof.
  induction p as [ | i m ed p IH ].
  - reflexivity.
  - simpl; rewrite IH, id_left; destruct i, m; exact He.
Qed.

(* The forward direction empty-path 论元 itself: compare the
 one-edge path against [tnil]. （已译） *)
Theorem loop_commutes_inv : Commutative LoopDiagram -> e ≈ id.
Proof.
  intro Hc.
  pose proof (Hc LpX LpX
                (tcons LpX (tt : @edges LoopQuiver LpX LpX) tnil) tnil) as H.
  simpl in H.
  now rewrite id_left in H.
Qed.

Theorem loop_commutes (He : e ≈ id) : Commutative LoopDiagram.
Proof.
  intros i j p q.
  now rewrite (loop_paths He _ _ p), (loop_paths He _ _ q).
Qed.

(* So walking loop, commutativity exactly statement the
 drawn endomorphism 恒等. This header claim about [tnil],
 proved rather than asserted. （已译） *)
Theorem loop_commutative_iff : Commutative LoopDiagram ↔ e ≈ id.
Proof.
  split.
  - apply loop_commutes_inv.
  - apply loop_commutes.
Qed.

End WalkingLoop.

(* * ** The 自然性 square commuting diagram （已译） *)

Section NaturalitySquare.

Context {C D : Category}.
Context {F G : C ⟶ D}.
Context (alpha : F ⟹ G).

(* The naturality square at [f : p ~> q], as a diagram of shape
   [SquareQuiver]:

        F p --fmap[F] f--> F q
         |                  |
       alpha p            alpha q
         |                  |
         v                  v
        G p --fmap[G] f--> G q                                            *)
Definition NaturalitySquareDiagram {p q : C} (f : p ~> q)
  : Diagram SquareQuiver D :=
  SquareDiagram (fmap[F] f) (@transform _ _ _ _ alpha q)
                (@transform _ _ _ _ alpha p) (fmap[G] f).

(* It commutes, 自然性. [naturality_sym] (Theory/Natural/Transformation.v)
 literally equation [square_commutes] asks for. （已译） *)
Theorem naturality_square_commutes {p q : C} (f : p ~> q) :
  Commutative (NaturalitySquareDiagram f).
Proof.
  apply square_commutes.
  apply naturality_sym.
Qed.

(* And commutativity diagram gives 自然性 back, so shape
 diagrammatic condition 自然性 equation same
 statement. （已译） *)
Theorem naturality_of_commutative_square {p q : C} (f : p ~> q) :
  Commutative (NaturalitySquareDiagram f) ->
  @transform _ _ _ _ alpha q ∘ fmap[F] f
    ≈ fmap[G] f ∘ @transform _ _ _ _ alpha p.
Proof.
  apply square_commutes_inv.
Qed.

Theorem naturality_square_commutative_iff {p q : C} (f : p ~> q) :
  Commutative (NaturalitySquareDiagram f)
    ↔ @transform _ _ _ _ alpha q ∘ fmap[F] f
        ≈ fmap[G] f ∘ @transform _ _ _ _ alpha p.
Proof.
  apply square_commutative_iff.
Qed.

End NaturalitySquare.


(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ShapeFactor {J C : Category} (F : J ⟶ C) (Hc : CommutativeShape F)
  : PreorderReflect J ⟶ C :=
  @QuotientLift J (TotalRel J) _ C F (fun x y f g _ => Hc x y f g).

Theorem commutative_shape_factors {J C : Category} (F : J ⟶ C)
        (Hc : CommutativeShape F) :
  ∀ (x y : J) (f : x ~> y),
    fmap[ShapeFactor F Hc] (fmap[Reflect J] f) = fmap[F] f.
Proof.
  intros. exact (@QuotientLift_proj J (TotalRel J) _ C F _ x y f).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* (<=) Anything of the form [K ◯ Reflect J] commutes, whatever [K] is. *)
Theorem factors_commutative_shape {J C : Category}
        (K : PreorderReflect J ⟶ C) :
  CommutativeShape (K ◯ Reflect J).
Proof.
  intros x y f g; simpl; apply fmap_respects; exact I.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem factors_commutative_shape' {J C : Category} (F : J ⟶ C)
        (K : PreorderReflect J ⟶ C)
        (Hobj : ∀ x : J, fobj[K] x = fobj[F] x)
        (Hfac : ∀ (x y : J) (f : x ~> y),
                   hom_cast (Hobj x) (Hobj y)
                     (fmap[K] (fmap[Reflect J] f)) ≈ fmap[F] f) :
  CommutativeShape F.
Proof.
  intros x y f g.
  rewrite <- (Hfac x y f), <- (Hfac x y g).
  apply hom_cast_respects.
  apply fmap_respects.
  exact I.
Qed.

(* And hence Mac Lane's quiver form predicate, through
 [commutative_iff_shape]: commuting diagram factors through preorder
 reflection FREE 范畴. （已译） *)
Theorem commutative_factors {G : Quiver} {C : Category} (D : Diagram G C)
        (Hc : Commutative D) :
  ∀ (x y : FreeOnQuiver G) (f : x ~> y),
    fmap[ShapeFactor (FunctorOfDiagram D) (fst (commutative_iff_shape D) Hc)]
        (fmap[Reflect _] f)
      = fmap[FunctorOfDiagram D] f.
Proof.
  intros. apply commutative_shape_factors.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FactorsThroughReflection {J C : Category} (F : J ⟶ C) : Type :=
  { K : PreorderReflect J ⟶ C &
  { Hobj : ∀ x : J, fobj[K] x = fobj[F] x &
    ∀ (x y : J) (f : x ~> y),
      hom_cast (Hobj x) (Hobj y)
        (fmap[K] (fmap[Reflect J] f)) ≈ fmap[F] f }}.

(* The factorization is moreover equality FUNCTORS StrictCat's
 hom-setoid, not merely pointwise agreement -- same 等价
 [functor_of_diagram_of_functor] above is stated in.（已译） *)
Lemma shape_factor_functor {J C : Category} (F : J ⟶ C) (Hc : CommutativeShape F) :
  @equiv _ (@Functor_StrictEq_Setoid J C) (ShapeFactor F Hc ◯ Reflect J) F.
Proof.
  exists (fun _ => eq_refl); intros; reflexivity.
Qed.

Theorem commutes_iff_factors {J C : Category} (F : J ⟶ C) :
  CommutativeShape F ↔ FactorsThroughReflection F.
Proof.
  split.
  - intro Hc.
    exists (ShapeFactor F Hc), (fun _ => eq_refl).
    (* 相关说明。 （已译） *)
    intros x y f; reflexivity.
  - intros [K [Hobj Hfac]].
    exact (factors_commutative_shape' F K Hobj Hfac).
Qed.
