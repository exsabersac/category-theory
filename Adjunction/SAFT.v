Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.

Set Universe Polymorphism.

Generalizable All Variables.

(** * The Special Adjoint Functor Theorem (SAFT) *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   特殊伴随函子定理 (SAFT) 是 GAFT 的特殊化：在更强假设下（例如合生成子、良幂等）
   把解集条件替换为更易检查的大小/生成条件。本文件陈述并证明 SAFT 及其刻画变体；
   与 [Adjunction/GAFT.v]、[Adjunction/SAFT/] 子目录配合。长技术短文本波次压缩为定义性
   导言；细节英文若仍残留于文内其它注释，属后续波次。 *)

(** ** Cogenerating families *)

(*
   本节说明 SAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record Cogenerator {C : Category} := {
  cog_index : Type;
  cog_obj : cog_index -> C;
  cog_separates : forall (x y : C) (f g : x ~> y),
    (forall (j : cog_index) (k : y ~> cog_obj j), k ∘ f ≈ k ∘ g) -> f ≈ g
}.

Arguments Cogenerator : clear implicits.
Arguments cog_index {C} _.
Arguments cog_obj {C} _ _.
Arguments cog_separates {C} _ {x y} f g _.

(** ** Well-powered indexing of subobjects *)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record SubobjectIndex {C : Category} (x : C) := {
  sub_index : Type;
  sub_dom : sub_index -> C;
  sub_mono : forall i, sub_dom i ~> x;
  sub_monic : forall i, Monic (sub_mono i)
}.

Arguments sub_index {C x} _.
Arguments sub_dom {C x} _ _.
Arguments sub_mono {C x} _ _.
Arguments sub_monic {C x} _ _.

(** ** [SubobjectIndex] does not give well-poweredness *)

(*
   本节说明伴随、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition empty_SubobjectIndex {C : Category} (x : C) : SubobjectIndex x :=
  {| sub_index := False ;
     sub_dom   := fun i => match i with end ;
     sub_mono  := fun i => match i with end ;
     sub_monic := fun i => match i with end |}.

(* ... and it cannot be completed to a well-powered index: there is no map
   from the subobjects of [x] into it, since [x] itself, along the identity,
   is a subobject. *)
Lemma SubobjectIndex_not_exhaustive {C : Category} (x : C) :
  (SubObj x -> sub_index (empty_SubobjectIndex x)) -> False.
Proof.
  intros f.
  exact (f {| Subobject.sub_dom := x ;
              Subobject.sub_mono := id ;
              Subobject.sub_is_monic := id_monic x |}).
Qed.

(** ** The product of the cogenerating family *)

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cogen_prod_limit {C : Category} (comp : @Complete C)
  (G : Cogenerator C) := comp _ (DiscreteCat_Functor (cog_obj G)).

Definition cogen_prod {C : Category} (comp : @Complete C)
  (G : Cogenerator C) : C :=
  iprod (cog_obj G) (cogen_prod_limit comp G).

(** ** The canonical map into a power of the cogenerating family *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The hom-indexed Σ-index of arrows out of [c] into the cogenerating family. *)
Definition cogen_power_index {C : Category} (G : Cogenerator C) (c : C) : Type :=
  { j : cog_index G & c ~> cog_obj G j }.

(* The family whose [(j, k)]-component is [cog_obj G j]. *)
Definition cogen_power_fam {C : Category} (G : Cogenerator C) (c : C) :
  cogen_power_index G c -> C :=
  fun p => cog_obj G (projT1 p).

(* Its product, drawn from completeness exactly as [cogen_prod_limit]. *)
Definition cogen_power_limit {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) :=
  comp _ (DiscreteCat_Functor (cogen_power_fam G c)).

Definition cogen_power {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) : C :=
  iprod (cogen_power_fam G c) (cogen_power_limit comp G c).

(* The family of legs [c ~> cog_obj G j] whose [(j, k)]-component is [k]. *)
Definition cogen_canonical_legs {C : Category} (G : Cogenerator C) (c : C) :
  forall p : cogen_power_index G c, c ~> cogen_power_fam G c p :=
  fun p => projT2 p.

(* The canonical map [c ~> cogen_power], the unique mediator of those legs. *)
Definition cogen_canonical {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) : c ~> cogen_power comp G c :=
  unique_obj (iprod_ump (cogen_power_fam G c) (cogen_power_limit comp G c)
                        c (cogen_canonical_legs G c)).

(*
   本节说明 SAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cogen_canonical_commutes {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) (j : cog_index G) (k : c ~> cog_obj G j) :
  iprod_proj (cogen_power_fam G c) (cogen_power_limit comp G c)
    (existT _ j k) ∘ cogen_canonical comp G c ≈ k.
Proof.
  exact (unique_property
           (iprod_ump (cogen_power_fam G c) (cogen_power_limit comp G c)
                      c (cogen_canonical_legs G c))
           (existT _ j k)).
Qed.

(*
   本节说明 SAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cogenerator_canonical_monic {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) : Monic (cogen_canonical comp G c).
Proof.
  constructor; intros z g1 g2 H.
  apply (cog_separates G g1 g2); intros j k.
  rewrite <- (cogen_canonical_commutes comp G c j k).
  rewrite <- !comp_assoc.
  now rewrite H.
Qed.

(** ** The covering datum and the solution set *)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SubobjectCover {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (G : Cogenerator C)
  (WP : forall x : C, SubobjectIndex x) : Type :=
  forall (d : D) (c : C) (h : d ~> U c),
    { i : sub_index (WP (cogen_prod comp G)) &
      { s : d ~> U (sub_dom (WP (cogen_prod comp G)) i) &
        { t : sub_dom (WP (cogen_prod comp G)) i ~> c &
          fmap[U] t ∘ s ≈ h } } }.

(*
   本节说明 SAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SubobjectCover_Id_retract {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (WP : forall x : C, SubobjectIndex x)
  (cover : SubobjectCover (@Id C) comp G WP) (c : C) :
  { i : sub_index (WP (cogen_prod comp G)) &
    { s : c ~> sub_dom (WP (cogen_prod comp G)) i &
      { t : sub_dom (WP (cogen_prod comp G)) i ~> c & t ∘ s ≈ id } } } :=
  cover c c id.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SAFT_solution_set@{i cobj dobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete C) (G : Cogenerator C)
  (WP : forall x : C, SubobjectIndex x)
  (cover : SubobjectCover U comp G WP) (d : D)
  : SolutionSet@{i dobj cobj h} U d.
Proof.
  unshelve refine
    {| sol_index := { i : sub_index (WP (cogen_prod comp G))
                      & d ~> U (sub_dom (WP (cogen_prod comp G)) i) }
     ; sol_obj := fun p => sub_dom (WP (cogen_prod comp G)) (projT1 p)
     ; sol_arr := fun p => projT2 p |}.
  intros c h.
  destruct (cover d c h) as [i [s [t e]]].
  exists (existT _ i s); simpl.
  exists t.
  exact e.
Defined.

(** ** The Special Adjoint Functor Theorem *)

(*
   本节说明伴随、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SAFT@{cobj dobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C D U)
  (G : Cogenerator C) (WP : forall x : C, SubobjectIndex x)
  (cover : SubobjectCover U comp G WP) : { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont (SAFT_solution_set U comp G WP cover).
