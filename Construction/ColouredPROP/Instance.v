Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.Quotient.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/strict+monoidal+category
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeColouredPROP.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The associator [(x ++ y) ++ z ≅ x ++ (y ++ z)] transported
 恒等 along [eq_sym (app_assoc x y z)] — orientation of
 [Cast.v]'s [to]. （已译） *)
Lemma CFreeCat_strict_assoc_to (x y z : list Colour) :
  to (@tensor_assoc (CFreeCat S) (CFreeCat_Monoidal S Cdec) x y z)
  ≈ match eq_sym (app_assoc x y z) in _ = T
      return ((x ++ y) ++ z ~{ CFreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(** The left unitor [[] ++ x ≅ x] transported 恒等 along
 [app_nil_l x] (definitionally trivial: [app] left-strict). （已译） *)
Lemma CFreeCat_strict_unit_left_to (x : list Colour) :
  to (@unit_left (CFreeCat S) (CFreeCat_Monoidal S Cdec) x)
  ≈ match app_nil_l x in _ = T
      return ([] ++ x ~{ CFreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(** The right unitor [x ++ [] ≅ x] transported 恒等 along
 [app_nil_r x] (a genuinely propositional equation). （已译） *)
Lemma CFreeCat_strict_unit_right_to (x : list Colour) :
  to (@unit_right (CFreeCat S) (CFreeCat_Monoidal S Cdec) x)
  ≈ match app_nil_r x in _ = T
      return (x ++ [] ~{ CFreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

Definition CFreeCat_Strict : @StrictMonoidal (CFreeCat S) := {|
  strict_is_monoidal    := CFreeCat_Monoidal S Cdec;  (* THE shared record *)
  strict_assoc_obj      := fun x y z => eq_sym (app_assoc x y z);
  strict_unit_left_obj  := fun x => app_nil_l x;
  strict_unit_right_obj := fun x => app_nil_r x;
  strict_assoc_to       := fun x y z => CFreeCat_strict_assoc_to x y z;
  strict_unit_left_to   := fun x => CFreeCat_strict_unit_left_to x;
  strict_unit_right_to  := fun x => CFreeCat_strict_unit_right_to x
|}.

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreeColouredPROP : ColouredPROP Colour :=
  Build_ColouredPROP Colour
    (CFreeCat S)
    CFreeCat_Strict
    (CFreeCat_Symmetric S Cdec)

    (* [strict_is_monoidal CFreeCat_Strict] and
       [braided_is_monoidal (symmetric_is_braided
        (CFreeCat_Symmetric S Cdec))] both reduce to the literal
       term [CFreeCat_Monoidal S Cdec].（标题）（已译） *)
    eq_refl

    (* 相关说明。 （已译） *)
    (fun cs : list Colour => cs)

    (* [I] of [CFreeCat_Monoidal S Cdec] is the literal [[]]. *)
    eq_refl

    (* [fobj (CFreeCat_Tensor S) (cs, ds)] reduces to [cs ++ ds]. *)
    (fun cs ds : list Colour => eq_refl).

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Instance CFreeCat_HomEqProp : HomEqProp (CFreeCat S) :=
  Build_HomEqProp (CFreeCat S)
    (fun cs ds : list Colour => @CTermEq Colour S cs ds)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H).

(* * Objects [CFreeCat S] are colour words, whose equality
 [list_eq_dec Cdec] decides. A [Definition], not [Instance]:
 it is [Cdec]-conditional (D2), call sites pass it explicitly
 so that exactly one 典范 decider circulates per colour
 type.（已译） *)

Definition CFreeCat_ObjDecEq : ObjDecEq (CFreeCat S) := list_eq_dec Cdec.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、（余）极限、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example FreeColouredPROP_coherence_is_refl :
  @cprop_monoidal_coherence Colour FreeColouredPROP = eq_refl := eq_refl.

(** The 对象 correspondence 恒等 colour words. （已译） *)
Example FreeColouredPROP_of_list_id (cs : list Colour) :
  cprop_of_list (ColouredPROP := FreeColouredPROP) cs = cs := eq_refl.

(** 本节：The monoidal unit THE shared record literal empty
 word. （已译） *)
Example FreeColouredPROP_I :
  @I (CFreeCat S) (CFreeCat_Monoidal S Cdec) = ([] : list Colour) := eq_refl.

(** 本节：The same unit, projected through bundled instance — pinning
 instance path shared record agree the
 nose. （已译） *)
Example FreeColouredPROP_I_instance :
  @I (CFreeCat S)
     (@strict_is_monoidal (CFreeCat S) (@cprop_strict Colour FreeColouredPROP))
  = ([] : list Colour) := eq_refl.

(** Tensor-on-对象 literally concatenation, [eq_refl]
 证明. （已译） *)
Example FreeColouredPROP_tensor_app_is_refl (cs ds : list Colour) :
  cprop_tensor_app (ColouredPROP := FreeColouredPROP) cs ds = eq_refl
  := eq_refl.

(** The singleton wire 对象 colour [c] literal
 one-element word [[c]]. （已译） *)
Example FreeColouredPROP_wire (c : Colour) :
  wire (P := FreeColouredPROP) c = [c] := eq_refl.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example FreeColouredPROP_cons_decomp (c : Colour) (cs : list Colour) :
  cprop_of_list (ColouredPROP := FreeColouredPROP) (c :: cs)
  = (wire (P := FreeColouredPROP) c
       ⨂[@strict_is_monoidal (CFreeCat S)
           (@cprop_strict Colour FreeColouredPROP)]
     cprop_of_list (ColouredPROP := FreeColouredPROP) cs)%object
  := eq_sym (cprop_tensor_app (ColouredPROP := FreeColouredPROP) [c] cs).

End FreeColouredPROP.

Arguments CFreeCat_Strict {Colour} S Cdec : assert.
Arguments FreeColouredPROP {Colour} S Cdec : assert.
Arguments CFreeCat_HomEqProp {Colour} S : assert.
(* [ObjDecEq] definitional (singleton) class, so 常值's
 论元 list continues two 对象 being compared. （已译） *)
Arguments CFreeCat_ObjDecEq {Colour} S Cdec x y : assert.
