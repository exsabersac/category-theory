Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Sieves, and the presheaf of sieves *)

(*
   本文件给出筛与层论相关定义。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* ------------------------------------------------------------------ *)
(** ** Sieves *)

(* A sieve on c: a Prop-valued membership on the arrows into c, closed
   under [≈] and under precomposition. *)

Record Sieve {C : Category} (c : C) := {
  sieve_mem : ∀ (d : C), (d ~> c) → Prop;

  (* membership does not distinguish ≈-equal arrows *)
  sieve_respects : ∀ (d : C) (f g : d ~> c),
      f ≈ g → sieve_mem d f → sieve_mem d g;

  (* Awodey's closure: f ∈ S implies f ∘ g ∈ S *)
  sieve_closed : ∀ (d e : C) (f : d ~> c) (g : e ~> d),
      sieve_mem d f → sieve_mem e (f ∘ g)
}.

Arguments sieve_mem {C c} _ {d} _.
Arguments sieve_respects {C c} _ {d} _ _ _ _.
Arguments sieve_closed {C c} _ {d e} _ _ _.

(* Two sieves are equivalent when they have the same members. *)
Definition sieve_equiv {C : Category} {c : C} : crelation (Sieve c) :=
  fun S T => ∀ (d : C) (f : d ~> c), sieve_mem S f <-> sieve_mem T f.

#[export]
Program Instance Sieve_Setoid {C : Category} (c : C) : Setoid (Sieve c) := {|
  equiv := sieve_equiv
|}.
Next Obligation.
  intros C c.
  constructor; repeat intro.
  - split; auto.
  - split; apply X.
  - split; intro H.
    + apply X0, X, H.
    + apply X, X0, H.
Qed.

(* Awodey's Ω(C), as an object of [Sets]. *)
Definition SieveObj {C : Category} (c : C) : SetoidObject := {|
  carrier := Sieve c ; is_setoid := Sieve_Setoid c
|}.

(* ------------------------------------------------------------------ *)
(** ** The total sieve, and restriction *)

(* Awodey's t_C = {f : · → C}: every arrow into c. *)
Program Definition total_sieve {C : Category} (c : C) : Sieve c := {|
  sieve_mem := fun _ _ => True
|}.
Next Obligation. intros; exact I. Qed.
Next Obligation. intros; exact I. Qed.

(* Awodey's h*(S) = {g | h ∘ g ∈ S}, for h : d ~> c in C. *)
Program Definition sieve_restrict {C : Category} {c d : C} (h : d ~> c)
        (S : Sieve c) : Sieve d := {|
  sieve_mem := fun e (g : e ~> d) => sieve_mem S (h ∘ g)
|}.
Next Obligation.
  intros C c d h S e f g Hfg Hmem.
  eapply sieve_respects; [ | exact Hmem ].
  now rewrite Hfg.
Qed.
Next Obligation.
  intros C c d h S e e' f g Hmem.
  eapply sieve_respects.
  - symmetry; apply comp_assoc.
  - now apply sieve_closed.
Qed.

(* Restriction carries the total sieve to the total sieve; this is the
   naturality content of the truth point built downstream. *)
Lemma sieve_restrict_total {C : Category} {c d : C} (h : d ~> c) :
  sieve_restrict h (total_sieve c) ≈ total_sieve d.
Proof. intros e g; split; intro; exact I. Qed.

Program Definition sieve_restrict_mor {C : Category} {c d : C} (h : d ~> c) :
  SieveObj c ~{Sets}~> SieveObj d := {|
  morphism := sieve_restrict h
|}.
Next Obligation.
  intros C c d h.
  unfold Proper, respectful; intros S T HST e g; simpl.
  split; intro H; now apply HST.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The presheaf of sieves *)

(*
   Awodey's Ω : C^op → Sets.  The three 函子定律 are the three

   本节说明相关定义、性质与动机。 范畴 laws C read through membership: respectfulness [fmap] is [筛_respects] at [h ≈ h'], identity law is [id_left] 复合 law is [comp_assoc].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Sieve_Presheaf (C : Category) : C^op ⟶ Sets := {|
  fobj := fun c => @SieveObj C c;
  fmap := fun x y (h : x ~{C^op}~> y) => @sieve_restrict_mor C x y h
|}.
Next Obligation.
  intros C x y.
  unfold Proper, respectful; intros h h2 Hh S d g; simpl.
  split; intro H; eapply sieve_respects; try exact H;
    [ now rewrite Hh | now rewrite Hh ].
Qed.
Next Obligation.
  intros C x S d f.
  simpl; split; intro H.
  - eapply sieve_respects; [ | exact H ]. apply id_left.
  - eapply sieve_respects; [ | exact H ]. symmetry; apply id_left.
Qed.
Next Obligation.
  intros C x y z f g S d k.
  simpl; split; intro H.
  - eapply sieve_respects; [ | exact H ]. symmetry; apply comp_assoc.
  - eapply sieve_respects; [ | exact H ]. apply comp_assoc.
Qed.
