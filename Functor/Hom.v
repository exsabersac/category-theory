Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The hom-functor Hom(-,-) : C^op ∏ C ⟶ Sets. *)

(* nLab: https://ncatlab.org/nlab/show/hom-functor
   Wikipedia: https://en.wikipedia.org/wiki/Hom_functor

   对（局部小）范畴 C，hom 函子把对象对 (a, b) 送到 hom 集 hom[C] a b，视为 Sets 的
   setoid 对象。对 C^op ∏ C 的态射——即对 (f, g)，f : a' ~{C}~> a（箭头 a ~{C^op}~> a'）
   且 g : b ~{C}~> b'——它把箭头 q : a ~> b 送到复合 g ∘ q ∘ f : a' ~> b'，即前复合 f、
   后复合 g。故双函子在第一变元反变、第二变元共变；等价地是 C 上的恒等双函子。

   固定一变元得到两个偏 hom 函子：共变 Hom(a, -) : C ⟶ Sets（后复合作用）与反变
   Hom(-, b) : C^op ⟶ Sets（前复合作用）。curry 形式 Curried_Hom : C^op ⟶ [C, Sets]
   打包共变族，作为满忠实嵌入即 Yoneda 嵌入（下文 Yoneda_Full 与 Yoneda_Faithful）；
   这是可表性的基础，见 Functor/Representable.v。因此处 hom 集是 setoid，Hom 落在
   setoid 范畴 Sets。 *)

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Hom `(C : Category) : C^op ∏ C ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom C (fst p) (snd p)
                    ; is_setoid := @homset (C) (fst p) (snd p) |};
  fmap := fun x y (f : x ~{C^op ∏ C}~> y) =>
            (* g ↦ snd f ∘ g ∘ fst f: post-compose with the C-component
               (covariant in the second argument), pre-compose with the
               C^op-component (contravariant in the first). *)
            {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.
Next Obligation. now rewrite !comp_assoc. Qed.

Program Definition Curried_Hom `(C : Category) : C^op ⟶ [C, Sets] := {|
  fobj := fun x => {|
    fobj := fun y => {| carrier := @hom C x y
                      ; is_setoid := @homset C x y |};
    fmap := fun y z (f : y ~{C}~> z) =>
              {| morphism := fun (g : x ~{C}~> y) =>
                               (f ∘ g) : x ~{C}~> z |}
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ op f |}
  |}
|}.
Next Obligation.
  simpl; intros.
  unfold op.
  apply comp_assoc.
Qed.

Coercion Curried_Hom : Category >-> Functor.

Notation "[Hom A , ─]" := (@Curried_Hom _ A) : functor_scope.

(*
   本节说明自然变换、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Yoneda_Faithful (C : Category) : Faithful (Curried_Hom C).
Proof.
  constructor.
  intros c c' f g same_nat_iso.
  simpl in same_nat_iso.
  specialize same_nat_iso with c id. now rewrite 2 id_left in same_nat_iso.
Qed.

(*
   本节说明自然变换、函子、Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Yoneda_Full (C : Category) : Full (Curried_Hom C).
Proof.
  unshelve econstructor; simpl in *.
  - exact (fun c d f => f c id).
  - abstract(intros x y [Ftrans Fnat ?] c f; simpl in *;
    unfold op;
    now rewrite Fnat, id_right).
Defined.

(*
   本节说明自然变换、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Yoneda_Embedding' (C: Category) (c d : C) :
  @IsIsomorphism Sets {| carrier := hom d c |}
                 {| carrier := hom (fobj[C] c) (fobj[C] d) |}
                 {| morphism := @fmap _ _ (Curried_Hom C) c d;
                            proper_morphism := fmap_respects _ _ |}.
Proof.
  apply bijective_is_iso.
  - abstract(assert (H := Yoneda_Faithful C); constructor;
             intros x y eq; apply H; exact eq).
  - constructor. simpl.
    intro A; exists (@prefmap _ _ _ (Yoneda_Full C) _ _ A ).
    abstract(intros x f; unfold op;
             assert (M := @fmap_sur _ _ _ (Yoneda_Full C));
             specialize M with _ _ A; simpl in M;
             unfold op in M; apply M).
Defined.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition CoHom_Alt `(C : Category) : C ∏ C^op ⟶ Sets :=
  Hom C ◯ Swap.

Program Definition CoHom `(C : Category) : C ∏ C^op ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom (C^op) (fst p) (snd p)
                    ; is_setoid := @homset (C^op) (fst p) (snd p) |};
  fmap := fun x y (f : x ~{C ∏ C^op}~> y) =>
    {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.
Next Obligation. now rewrite <- ! comp_assoc. Qed.

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Curried_CoHom `(C : Category) : C ⟶ [C^op, Sets] :=
  Curried_Hom C^op.

Notation "[Hom ─ , A ]" := (@Curried_CoHom _ A) : functor_scope.
