Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.
Require Import Category.Construction.DecoratedCospan.Symmetric.

Generalizable All Variables.

(*
    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872,
    nLab: https://ncatlab.org/nlab/show/decorated+cospan
    Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DecoratedCospanMonoidal.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.
Context `{DCBC : @DecCospan_Bifunctor_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.

Notation DC := (DecoratedCospanCat HP LM id_decoration cospan_merge).

(** Local aliases that fix the [LM], [cospan_merge], [id_decoration]
    arguments to those of the ambient section, so the proofs below
    don't have to re-pass them at every use. *)

Notation Dtensor f g := (dec_cospan_tensor LM cospan_merge f g).
Notation Dcompose g f := (dec_cospan_compose HP LM cospan_merge g f).
Notation Did X := (dec_cospan_id id_decoration X).
Notation Dlift f := (dec_mor_as_cospan id_decoration f).

(*
   本节说明幺半结构、幺半群、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class DecCospan_Monoidal_Coherent : Type := {

  (** Naturality of [to (unit_left)]: as a decorated-cospan equation. *)
  dec_to_unit_left_natural_eq :
    forall {x y : C} (g : DecoratedCospanArrow x y),
      dec_cospan_equiv
        (Dcompose g (Dlift (to (@coprod_zero_l C H_Coc H_Ini x))))
        (Dcompose (Dlift (to (@coprod_zero_l C H_Coc H_Ini y)))
                  (Dtensor (Did 0%object) g));

  (** Naturality of [from (unit_left)]. *)
  dec_from_unit_left_natural_eq :
    forall {x y : C} (g : DecoratedCospanArrow x y),
      dec_cospan_equiv
        (Dcompose (Dtensor (Did 0%object) g)
                  (Dlift (from (@coprod_zero_l C H_Coc H_Ini x))))
        (Dcompose (Dlift (from (@coprod_zero_l C H_Coc H_Ini y))) g);

  (** Naturality of [to (unit_right)]. *)
  dec_to_unit_right_natural_eq :
    forall {x y : C} (g : DecoratedCospanArrow x y),
      dec_cospan_equiv
        (Dcompose g (Dlift (to (@coprod_zero_r C H_Coc H_Ini x))))
        (Dcompose (Dlift (to (@coprod_zero_r C H_Coc H_Ini y)))
                  (Dtensor g (Did 0%object)));

  (** Naturality of [from (unit_right)]. *)
  dec_from_unit_right_natural_eq :
    forall {x y : C} (g : DecoratedCospanArrow x y),
      dec_cospan_equiv
        (Dcompose (Dtensor g (Did 0%object))
                  (Dlift (from (@coprod_zero_r C H_Coc H_Ini x))))
        (Dcompose (Dlift (from (@coprod_zero_r C H_Coc H_Ini y))) g);

  (** Naturality of [to (tensor_assoc)]. *)
  dec_to_tensor_assoc_natural_eq :
    forall {x y z w v u : C}
           (g : DecoratedCospanArrow x y)
           (h : DecoratedCospanArrow z w)
           (i : DecoratedCospanArrow v u),
      dec_cospan_equiv
        (Dcompose (Dtensor g (Dtensor h i))
                  (Dlift (to (@coprod_assoc C H_Coc x z v))))
        (Dcompose (Dlift (to (@coprod_assoc C H_Coc y w u)))
                  (Dtensor (Dtensor g h) i));

  (** Naturality of [from (tensor_assoc)]. *)
  dec_from_tensor_assoc_natural_eq :
    forall {x y z w v u : C}
           (g : DecoratedCospanArrow x y)
           (h : DecoratedCospanArrow z w)
           (i : DecoratedCospanArrow v u),
      dec_cospan_equiv
        (Dcompose (Dtensor (Dtensor g h) i)
                  (Dlift (from (@coprod_assoc C H_Coc x z v))))
        (Dcompose (Dlift (from (@coprod_assoc C H_Coc y w u)))
                  (Dtensor g (Dtensor h i)));

  (** Triangle identity. *)
  dec_triangle_identity_eq :
    forall {x y : C},
      dec_cospan_equiv
        (Dtensor (Dlift (to (@coprod_zero_r C H_Coc H_Ini x))) (Did y))
        (Dcompose (Dtensor (Did x)
                           (Dlift (to (@coprod_zero_l C H_Coc H_Ini y))))
                  (Dlift (to (@coprod_assoc C H_Coc x 0%object y))));

  (** Pentagon identity.

      LHS reads (right-to-left, as Coq composes):
        [bimap α_{xyz} id_w] : ((x+y)+z)+w → (x+(y+z))+w
        [α_{x,(y+z),w}]      : (x+(y+z))+w → x+((y+z)+w)
        [bimap id_x α_{yzw}] : x+((y+z)+w) → x+(y+(z+w))
      RHS: [α_{x,y,(z+w)} ∘ α_{(x+y),z,w}]
        ((x+y)+z)+w → (x+y)+(z+w) → x+(y+(z+w)). *)
  dec_pentagon_identity_eq :
    forall {x y z w : C},
      dec_cospan_equiv
        (Dcompose
           (Dtensor (Did x) (Dlift (to (@coprod_assoc C H_Coc y z w))))
           (Dcompose
              (Dlift (to (@coprod_assoc C H_Coc x (y + z)%object w)))
              (Dtensor (Dlift (to (@coprod_assoc C H_Coc x y z))) (Did w))))
        (Dcompose
           (Dlift (to (@coprod_assoc C H_Coc x y (z + w)%object)))
           (Dlift (to (@coprod_assoc C H_Coc (x + y)%object z w))));

  (*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  dec_iso_lift_to_from :
    forall {X Y : C} (phi : X ≅ Y),
      dec_cospan_equiv
        (Dcompose (Dlift (to phi)) (Dlift (from phi)))
        (Did Y);

  dec_iso_lift_from_to :
    forall {X Y : C} (phi : X ≅ Y),
      dec_cospan_equiv
        (Dcompose (Dlift (from phi)) (Dlift (to phi)))
        (Did X)
}.

Context `{DCMC : DecCospan_Monoidal_Coherent}.

Set Default Proof Using "All".

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition DecoratedCospan_Monoidal : @Monoidal DC := {|
  I := (@initial_obj C H_Ini : DC);
  tensor := DecoratedCospan_Bifunctor HP LM id_decoration cospan_merge;
  unit_left :=
    fun X => {| to   := Dlift (to (@coprod_zero_l C H_Coc H_Ini X));
                from := Dlift (from (@coprod_zero_l C H_Coc H_Ini X));
                iso_to_from := _;
                iso_from_to := _ |};
  unit_right :=
    fun X => {| to   := Dlift (to (@coprod_zero_r C H_Coc H_Ini X));
                from := Dlift (from (@coprod_zero_r C H_Coc H_Ini X));
                iso_to_from := _;
                iso_from_to := _ |};
  tensor_assoc :=
    fun X Y Z => {| to   := Dlift (to (@coprod_assoc C H_Coc X Y Z));
                    from := Dlift (from (@coprod_assoc C H_Coc X Y Z));
                    iso_to_from := _;
                    iso_from_to := _ |}
|}.
Next Obligation. apply (dec_iso_lift_to_from (@coprod_zero_l C H_Coc H_Ini X)). Qed.
Next Obligation. apply (dec_iso_lift_from_to (@coprod_zero_l C H_Coc H_Ini X)). Qed.
Next Obligation. apply (dec_iso_lift_to_from (@coprod_zero_r C H_Coc H_Ini X)). Qed.
Next Obligation. apply (dec_iso_lift_from_to (@coprod_zero_r C H_Coc H_Ini X)). Qed.
Next Obligation. apply (dec_iso_lift_to_from (@coprod_assoc C H_Coc X Y Z)). Qed.
Next Obligation. apply (dec_iso_lift_from_to (@coprod_assoc C H_Coc X Y Z)). Qed.
Next Obligation. apply dec_to_unit_left_natural_eq. Qed.
Next Obligation. apply dec_from_unit_left_natural_eq. Qed.
Next Obligation. apply dec_to_unit_right_natural_eq. Qed.
Next Obligation. apply dec_from_unit_right_natural_eq. Qed.
Next Obligation. apply dec_to_tensor_assoc_natural_eq. Qed.
Next Obligation. apply dec_from_tensor_assoc_natural_eq. Qed.
Next Obligation. apply dec_triangle_identity_eq. Qed.
Next Obligation.
  (* Reassociate via dec_cospan_compose_assoc_sym, then apply the proved identity. *)
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge).
  }
  apply dec_pentagon_identity_eq.
Qed.

End DecoratedCospanMonoidal.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
