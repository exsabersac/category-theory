Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/strict+monoidal+category
    Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category#Strict_monoidal_category

   本文件给出严格情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section StrictMonoidal.

Context {C : Category}.

Class StrictMonoidal : Type := {
  strict_is_monoidal : @Monoidal C;

  (** Object-level strictness. *)
  strict_assoc_obj :
    forall (X Y Z : C),
      ((X ⨂[strict_is_monoidal] Y)%object ⨂[strict_is_monoidal] Z)%object
      = (X ⨂[strict_is_monoidal] (Y ⨂[strict_is_monoidal] Z)%object)%object;

  strict_unit_left_obj :
    forall (X : C),
      (I ⨂[strict_is_monoidal] X)%object = X;

  strict_unit_right_obj :
    forall (X : C),
      (X ⨂[strict_is_monoidal] I)%object = X;

  (** The structural isomorphisms ARE the identity, transported.

      We use the [match] form (rather than [eq_rect]) to keep
      destruct-of-equality reductions clean. *)
  strict_assoc_to :
    forall (X Y Z : C),
      to (@tensor_assoc C strict_is_monoidal X Y Z)
      ≈ match strict_assoc_obj X Y Z in _ = T
          return ((X ⨂[strict_is_monoidal] Y)%object
                   ⨂[strict_is_monoidal] Z)%object ~> T
        with eq_refl => id end;

  strict_unit_left_to :
    forall (X : C),
      to (@unit_left C strict_is_monoidal X)
      ≈ match strict_unit_left_obj X in _ = T
          return (I ⨂[strict_is_monoidal] X)%object ~> T
        with eq_refl => id end;

  strict_unit_right_to :
    forall (X : C),
      to (@unit_right C strict_is_monoidal X)
      ≈ match strict_unit_right_obj X in _ = T
          return (X ⨂[strict_is_monoidal] I)%object ~> T
        with eq_refl => id end
}.
#[export] Existing Instance strict_is_monoidal.

Coercion strict_is_monoidal : StrictMonoidal >-> Monoidal.

(** ** Corollaries

    In a strict monoidal category the [from] direction of each
    structural iso is also the transported identity. *)

Context `{S : StrictMonoidal}.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma strict_assoc_iso (X Y Z : C) :
  to (@tensor_assoc C strict_is_monoidal X Y Z)
    ∘ from (@tensor_assoc C strict_is_monoidal X Y Z)
  ≈ id.
Proof. apply iso_to_from. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma transported_iso_from
  {C' : Category} {a b : C'} (e : a = b) (phi : a ≅[C'] b)
  (Hto : to phi ≈ match e in _ = T return a ~> T with eq_refl => id end) :
  from phi ≈ match e in _ = T return T ~> a with eq_refl => id end.
Proof.
  pose proof (iso_to_from phi) as Htf.
  rewrite Hto in Htf.
  destruct e.
  simpl in Htf |- *.
  rewrite id_left in Htf.
  exact Htf.
Qed.

Lemma strict_assoc_from (X Y Z : C) :
  from (@tensor_assoc C strict_is_monoidal X Y Z)
  ≈ match strict_assoc_obj X Y Z in _ = T
      return T ~> ((X ⨂[strict_is_monoidal] Y)%object
                    ⨂[strict_is_monoidal] Z)%object
    with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (strict_assoc_obj X Y Z)
           (@tensor_assoc C _ X Y Z)).
  apply strict_assoc_to.
Qed.

Lemma strict_unit_left_from (X : C) :
  from (@unit_left C strict_is_monoidal X)
  ≈ match strict_unit_left_obj X in _ = T
      return T ~> (I ⨂[strict_is_monoidal] X)%object
    with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (strict_unit_left_obj X)
           (@unit_left C _ X)).
  apply strict_unit_left_to.
Qed.

Lemma strict_unit_right_from (X : C) :
  from (@unit_right C strict_is_monoidal X)
  ≈ match strict_unit_right_obj X in _ = T
      return T ~> (X ⨂[strict_is_monoidal] I)%object
    with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (strict_unit_right_obj X)
           (@unit_right C _ X)).
  apply strict_unit_right_to.
Qed.

End StrictMonoidal.

(*
   本节说明 Strict 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
