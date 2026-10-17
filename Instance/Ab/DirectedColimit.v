(*
   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Subgroups of an abelian group *)

(*
   本节说明 DirectedColimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record AbSubgroup (A : AbObject) := {
  absub_mem : carrier (cmon_setoid A) → Type;

  absub_resp : ∀ a b : carrier (cmon_setoid A),
    a ≈ b → absub_mem a → absub_mem b;
  absub_zero : absub_mem (cmon_zero A);
  absub_plus : ∀ a b : carrier (cmon_setoid A),
    absub_mem a → absub_mem b → absub_mem (cmon_plus A a b);
  absub_neg : ∀ a : carrier (cmon_setoid A),
    absub_mem a → absub_mem (ab_neg A a)
}.

Arguments absub_mem {A} _ _.
Arguments absub_resp {A} _ _ _ _ _.
Arguments absub_zero {A} _.
Arguments absub_plus {A} _ _ _ _ _.
Arguments absub_neg {A} _ _ _.

(** ** A subgroup as an object of Ab *)

(*
   本节说明 DirectedColimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section Subgroup.

Context {A : AbObject}.
Context (S : AbSubgroup A).

Definition absub_carrier : Type :=
  { a : carrier (cmon_setoid A) & absub_mem S a }.

Program Definition absub_setoid : Setoid absub_carrier := {|
  equiv := fun p q => projT1 p ≈ projT1 q
|}.

Definition AbSubgroupAb : AbObject.
Proof using A S.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := absub_carrier
                         ; is_setoid := absub_setoid |}
       ; cmon_zero := existT _ (cmon_zero A) (absub_zero S)
       ; cmon_plus := fun p q =>
           existT _ (cmon_plus A (projT1 p) (projT1 q))
                    (absub_plus S _ _ (projT2 p) (projT2 q))
       (* 相关说明。 （已译） *)
       ; cmon_prop :=
           sigma_first_PropEquiv absub_setoid
             (fun _ _ h => h) (fun _ _ h => h) (cmon_prop A) |};
    ab_neg := fun p =>
      existT _ (ab_neg A (projT1 p)) (absub_neg S _ (projT2 p))
  |}.
  - intros p p' Hp q q' Hq; simpl in *; now rewrite Hp, Hq.
  - intros a b c; simpl; apply cmon_plus_assoc.
  - intros a b; simpl; apply cmon_plus_comm.
  - intros a; simpl; apply cmon_plus_zero_l.
  - intros p q Hpq; simpl in *; now rewrite Hpq.
  - intros a; simpl; apply ab_neg_left.
Defined.

(*
   本节说明 DirectedColimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition absub_incl : AbSubgroupAb ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun p : absub_carrier => projT1 p |} |}.

End Subgroup.

Arguments absub_carrier {A} _.
Arguments AbSubgroupAb {A} _.
Arguments absub_incl {A} _.

(* 相关说明。 （已译） *)

(* [Type]-valued membership in a list, up to `≈'.  [Empty_set] is [Set], so
   it sits below every [Type@{i}] and needs no polymorphic empty type. *)
Fixpoint mem_list {A : AbObject} (a : carrier (cmon_setoid A))
  (l : list (carrier (cmon_setoid A))) : Type :=
  match l with
  | nil => Empty_set
  | x :: l' => ((x ≈ a) + mem_list a l')%type
  end.

Lemma mem_list_here {A : AbObject} (a : carrier (cmon_setoid A))
  (l : list (carrier (cmon_setoid A))) : mem_list a (a :: l).
Proof. exact (inl (reflexivity a)). Defined.

Lemma mem_list_app_l {A : AbObject} (x : carrier (cmon_setoid A))
  (l m : list (carrier (cmon_setoid A))) :
  mem_list x l → mem_list x (l ++ m).
Proof.
  induction l as [|y l IH]; simpl.
  - intro e; destruct e.
  - intros [Hy | Hl].
    + exact (inl Hy).
    + exact (inr (IH Hl)).
Defined.

Lemma mem_list_app_r {A : AbObject} (x : carrier (cmon_setoid A))
  (l m : list (carrier (cmon_setoid A))) :
  mem_list x m → mem_list x (l ++ m).
Proof.
  induction l as [|y l IH]; simpl.
  - exact (fun h => h).
  - exact (fun h => inr (IH h)).
Defined.

(*
   本节说明 DirectedColimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive InGen (A : AbObject) (l : list (carrier (cmon_setoid A)))
  : carrier (cmon_setoid A) → Type :=
  | ig_gen (a : carrier (cmon_setoid A)) : mem_list a l → InGen a
  | ig_zero : InGen (cmon_zero A)
  | ig_plus (a b : carrier (cmon_setoid A)) :
      InGen a → InGen b → InGen (cmon_plus A a b)
  | ig_neg (a : carrier (cmon_setoid A)) :
      InGen a → InGen (ab_neg A a)
  | ig_resp (a b : carrier (cmon_setoid A)) :
      a ≈ b → InGen a → InGen b.

Arguments ig_gen {A l} _ _.
Arguments ig_zero {A l}.
Arguments ig_plus {A l} _ _ _ _.
Arguments ig_neg {A l} _ _.
Arguments ig_resp {A l} _ _ _ _.

(* 相关说明。 （已译） *)
Definition gen_sub (A : AbObject) (l : list (carrier (cmon_setoid A)))
  : AbSubgroup A := {|
  absub_mem := @InGen A l;
  absub_resp := @ig_resp A l;
  absub_zero := @ig_zero A l;
  absub_plus := @ig_plus A l;
  absub_neg := @ig_neg A l
|}.

(*
   本节说明 DirectedColimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma gen_least (A : AbObject) (l : list (carrier (cmon_setoid A)))
  (S : AbSubgroup A) (H : ∀ x, mem_list x l → absub_mem S x) :
  ∀ a, InGen A l a → absub_mem S a.
Proof.
  intros a Ha.
  induction Ha as [a Hm | | a b _ IHa _ IHb | a _ IHa | a b Hab _ IHa].
  - exact (H a Hm).
  - exact (absub_zero S).
  - exact (absub_plus S _ _ IHa IHb).
  - exact (absub_neg S _ IHa).
  - exact (absub_resp S _ _ Hab IHa).
Defined.

Definition gen_mono (A : AbObject)
  (l m : list (carrier (cmon_setoid A)))
  (H : ∀ x, mem_list x l → InGen A m x) :
  ∀ a, InGen A l a → InGen A m a :=
  gen_least A l (gen_sub A m) H.

(* * * Finitely generated subgroups, index 范畴 （已译） *)

(*
   本节说明 DirectedColimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record FinGen (A : AbObject) (S : AbSubgroup A) := {
  fg_list : list (carrier (cmon_setoid A));

  fg_into : ∀ a, absub_mem S a → InGen A fg_list a;
  fg_from : ∀ a, InGen A fg_list a → absub_mem S a
}.

Arguments fg_list {A S} _.
Arguments fg_into {A S} _ _ _.
Arguments fg_from {A S} _ _ _.

Definition FGObj (A : AbObject) : Type := { S : AbSubgroup A & FinGen A S }.

Definition fg_sub {A : AbObject} (X : FGObj A) : AbSubgroup A := projT1 X.

Definition fg_pres {A : AbObject} (X : FGObj A) : FinGen A (fg_sub X) :=
  projT2 X.

Definition fg_gens {A : AbObject} (X : FGObj A)
  : list (carrier (cmon_setoid A)) := fg_list (fg_pres X).

Definition FGHom (A : AbObject) (X Y : FGObj A) : Type :=
  ∀ a, absub_mem (fg_sub X) a → absub_mem (fg_sub Y) a.

(* The index 范畴. The hom-setoid is trivially-true one of
 Instance/Proset.v, so every categorical law is 自由; [Proset] itself
 is unusable here because its homs must be [Prop]-valued (header).（已译） *)
Program Definition FGSub (A : AbObject) : Category := {|
  obj     := FGObj A;
  hom     := FGHom A;
  homset  := fun _ _ => {| Setoid.equiv := fun _ _ => True |};
  id      := fun _ _ p => p;
  compose := fun _ _ _ f g a p => f a (g a p)
|}.

(* * ** Presented 对象, directedness list concatenation （已译） *)

(* A list presents subgroup it generates, both legs 恒等
 function -- payoff [gen_sub]'s fields being constructors. （已译） *)
Definition fingen_gen (A : AbObject) (l : list (carrier (cmon_setoid A)))
  : FinGen A (gen_sub A l) :=
  Build_FinGen A (gen_sub A l) l (fun _ p => p) (fun _ p => p).

Definition fg_of_list (A : AbObject) (l : list (carrier (cmon_setoid A)))
  : FGObj A := existT _ (gen_sub A l) (fingen_gen A l).

(* Directedness is list concatenation. *)
Definition fg_join {A : AbObject} (X Y : FGObj A) : FGObj A :=
  fg_of_list A (fg_gens X ++ fg_gens Y).

Definition fg_join_left {A : AbObject} (X Y : FGObj A)
  : X ~{FGSub A}~> fg_join X Y :=
  fun a p =>
    gen_mono A (fg_gens X) (fg_gens X ++ fg_gens Y)
      (fun x h => ig_gen x (mem_list_app_l x _ _ h))
      a (fg_into (fg_pres X) a p).

Definition fg_join_right {A : AbObject} (X Y : FGObj A)
  : Y ~{FGSub A}~> fg_join X Y :=
  fun a p =>
    gen_mono A (fg_gens Y) (fg_gens X ++ fg_gens Y)
      (fun x h => ig_gen x (mem_list_app_r x _ _ h))
      a (fg_into (fg_pres Y) a p).

(** The exercise's word "directed": any two 对象 index jointly
 dominated third, namely subgroup presented concatenation
 two lists generators. （已译） *)
Lemma FGSub_directed {A : AbObject} (X Y : FGObj A) :
  { Z : FGSub A & ((X ~{FGSub A}~> Z) * (Y ~{FGSub A}~> Z))%type }.
Proof.
  exists (fg_join X Y).
  exact (fg_join_left X Y, fg_join_right X Y).
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition FGDiagram (A : AbObject) : FGSub A ⟶ Ab := {|
  fobj := fun X => AbSubgroupAb (fg_sub X);
  fmap := fun X Y f =>
    {| cmon_map :=
         {| morphism := fun p => existT _ (projT1 p) (f (projT1 p) (projT2 p))
          |} |}
|}.

(* The cocone whose universality 定理: apex [A], legs the
 inclusions. （已译） *)
Program Definition FGCocone (A : AbObject) : Cocone (FGDiagram A) := {|
  vertex_obj := A;
  coneFrom   := {| vertex_map := fun X => absub_incl (fg_sub X) |}
|}.

(* 相关说明。 （已译） *)

Section Mediator.

Context {A : AbObject}.
Context (N : Cocone (FGDiagram A)).

(* 相关说明。 （已译） *)
Definition nu_val (X : FGObj A) (a : carrier (cmon_setoid A))
  (p : absub_mem (fg_sub X) a) : carrier (cmon_setoid vertex_obj[N]) :=
  cmon_map (cocone_inj N X) (existT _ a p).

Lemma nu_transport (X Y : FGObj A) (f : X ~{FGSub A}~> Y)
  (a : carrier (cmon_setoid A)) (p : absub_mem (fg_sub X) a) :
  nu_val Y a (f a p) ≈ nu_val X a p.
Proof using A N. exact (cocone_inj_coherence N f (existT _ a p)). Qed.

(* * The master 融贯性 引理: cocone's legs agree any two
 memberships any two 对象, at ≈-equal elements. Everything below is
 application it, it is exactly where directedness is spent.（已译） *)
Lemma med_coherent (X Y : FGObj A) (a b : carrier (cmon_setoid A))
  (p : absub_mem (fg_sub X) a) (q : absub_mem (fg_sub Y) b) (Hab : a ≈ b) :
  nu_val X a p ≈ nu_val Y b q.
Proof using A N.
  rewrite <- (nu_transport X (fg_join X Y) (fg_join_left X Y) a p).
  rewrite <- (nu_transport Y (fg_join X Y) (fg_join_right X Y) b q).
  unfold nu_val.
  apply proper_morphism; exact Hab.
Qed.

(** 本节：The cyclic subgroup one element, distinguished member. （已译） *)

Definition cyc (a : carrier (cmon_setoid A)) : FGObj A :=
  fg_of_list A (a :: nil).

Definition cyc_mem (a : carrier (cmon_setoid A))
  : absub_mem (fg_sub (cyc a)) a := ig_gen a (mem_list_here a nil).

Definition med_fun (a : carrier (cmon_setoid A))
  : carrier (cmon_setoid vertex_obj[N]) := nu_val (cyc a) a (cyc_mem a).

Lemma med_fun_at (X : FGObj A) (a : carrier (cmon_setoid A))
  (p : absub_mem (fg_sub X) a) : med_fun a ≈ nu_val X a p.
Proof using A N.
  exact (med_coherent (cyc a) X a a (cyc_mem a) p (reflexivity a)).
Qed.

Lemma med_fun_respects : Proper (equiv ==> equiv) med_fun.
Proof using A N.
  intros a b Hab.
  exact (med_coherent (cyc a) (cyc b) a b (cyc_mem a) (cyc_mem b) Hab).
Qed.

Lemma med_fun_zero : med_fun (cmon_zero A) ≈ cmon_zero vertex_obj[N].
Proof using A N.
  rewrite (med_fun_at (cyc (cmon_zero A)) (cmon_zero A)
             (absub_zero (fg_sub (cyc (cmon_zero A))))).
  exact (cmon_map_zero (cocone_inj N (cyc (cmon_zero A)))).
Qed.

Lemma med_fun_plus (a b : carrier (cmon_setoid A)) :
  med_fun (cmon_plus A a b)
    ≈ cmon_plus vertex_obj[N] (med_fun a) (med_fun b).
Proof using A N.
  pose (Z := fg_of_list A (a :: b :: nil)).
  pose (pa := ig_gen (l := a :: b :: nil) a (mem_list_here a (b :: nil))).
  pose (pb := ig_gen (l := a :: b :: nil) b
                (inr (mem_list_here b nil))).
  rewrite (med_fun_at Z a pa), (med_fun_at Z b pb).
  rewrite (med_fun_at Z (cmon_plus A a b)
             (absub_plus (fg_sub Z) a b pa pb)).
  exact (cmon_map_plus (cocone_inj N Z) (existT _ a pa) (existT _ b pb)).
Qed.

(* The mediator: evaluate competing cocone at cyclic 对象 the
 element itself. All three [CMonHom] fields supplied name, so no
 obligation generated. （已译） *)
Program Definition fg_med : A ~{Ab}~> vertex_obj[N] := {|
  cmon_map := {| morphism := med_fun ; proper_morphism := med_fun_respects |};
  cmon_map_zero := med_fun_zero;
  cmon_map_plus := med_fun_plus
|}.

End Mediator.

(* * * The 定理: A colimit finitely generated subgroups （已译） *)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fg_med_commutes {A : AbObject} (N : Cocone (FGDiagram A))
  (X : FGSub A) :
  fg_med N ∘ cocone_inj (FGCocone A) X ≈ cocone_inj N X.
Proof.
  intro z; destruct z as [a p].
  exact (med_fun_at N X a p).
Qed.

Lemma fg_med_unique {A : AbObject} (N : Cocone (FGDiagram A))
  (v : A ~{Ab}~> vertex_obj[N])
  (Hv : ∀ X : FGSub A, v ∘ cocone_inj (FGCocone A) X ≈ cocone_inj N X) :
  fg_med N ≈ v.
Proof.
  intro a.
  symmetry.
  exact (Hv (cyc a) (existT _ a (cyc_mem a))).
Qed.

(* Mac Lane §III.3 Exercise 7: the inclusion cocone is universal. *)
Definition ab_fg_colimit (A : AbObject) : IsColimitCocone (FGCocone A).
Proof.
  intro M.
  unshelve refine {| unique_obj := fg_med M |}.
  - exact (fg_med_commutes M).
  - exact (fg_med_unique M).
Defined.

(* 相关说明。 （已译） *)
Definition ab_fg_isacolimit (A : AbObject) : IsAColimit (FGDiagram A) A :=
  colimitcocone_isacolimit (ab_fg_colimit A).

Definition ab_fg_Colimit (A : AbObject) : Colimit (FGDiagram A) :=
  limitcone_limit (FGCocone A) (ab_fg_colimit A).

(* 相关说明。 （已译） *)

Example fg_cocone_apex (A : AbObject) : vertex_obj[FGCocone A] = A := eq_refl.

Example fg_cocone_leg (A : AbObject) (X : FGSub A) :
  cocone_inj (FGCocone A) X = absub_incl (fg_sub X) := eq_refl.

Example fg_med_value (A : AbObject) (N : Cocone (FGDiagram A))
  (a : carrier (cmon_setoid A)) :
  cmon_map (fg_med N) a = nu_val N (cyc a) a (cyc_mem a) := eq_refl.

(** Membership generated subgroup IS inductive family, is
 what makes both legs [fingen_gen] 恒等 function. （已译） *)
Example gen_sub_mem (A : AbObject) (l : list (carrier (cmon_setoid A))) :
  absub_mem (gen_sub A l) = InGen A l := eq_refl.

Example fg_sub_of_list (A : AbObject) (l : list (carrier (cmon_setoid A))) :
  fg_sub (fg_of_list A l) = gen_sub A l := eq_refl.

(** 本节：The diagram's arrow action moves no element: it retags membership
 witness leaves underlying element alone. （已译） *)
Example fg_diagram_fmap_elem (A : AbObject) (X Y : FGSub A)
  (f : X ~{FGSub A}~> Y) (p : carrier (cmon_setoid (FGDiagram A X))) :
  projT1 (cmon_map (@fmap _ _ (FGDiagram A) X Y f) p) = projT1 p := eq_refl.

(** 本节：The index thin, so any two parallel inclusions identified. （已译） *)
Lemma FGSub_Thin (A : AbObject) : Thin (FGSub A).
Proof. intros X Y f g; exact I. Qed.

(** * Non-vacuity over the integers *)

(* [Instance/Ab/Coproduct.v]'s [ab_Z] is [ring_ab Int_Ring], additive
 group Theory/Algebra/Rig.v's axiom-自由 integers. It is reused here;
 no new group is built, [ab_Z]'s `≈` is Leibniz equality [Z]
 ([Z_eqT]), which is what makes computations below close [eq_refl].（已译） *)

(* 相关说明。 （已译） *)

Lemma Zmult_resp (d : Z) : ∀ a b : carrier (cmon_setoid ab_Z),
  a ≈ b → Z.divide d a → Z.divide d b.
Proof.
  intros a b Hab H.
  assert (a = b) as E by exact Hab.
  now rewrite <- E.
Qed.

Lemma Zmult_zero (d : Z) : Z.divide d (cmon_zero ab_Z).
Proof. apply Z.divide_0_r. Qed.

Lemma Zmult_plus (d : Z) : ∀ a b : carrier (cmon_setoid ab_Z),
  Z.divide d a → Z.divide d b → Z.divide d (cmon_plus ab_Z a b).
Proof. intros a b Ha Hb; now apply Z.divide_add_r. Qed.

Lemma Zmult_neg (d : Z) : ∀ a : carrier (cmon_setoid ab_Z),
  Z.divide d a → Z.divide d (ab_neg ab_Z a).
Proof. intros a Ha; now apply Z.divide_opp_r. Qed.

Definition Zmultiples (d : Z) : AbSubgroup ab_Z :=
  Build_AbSubgroup ab_Z (fun a => Z.divide d a)
    (Zmult_resp d) (Zmult_zero d) (Zmult_plus d) (Zmult_neg d).

(* 相关说明。 （已译） *)

Definition Ztwo : FGObj ab_Z := fg_of_list ab_Z (2%Z :: nil).
Definition Zthree : FGObj ab_Z := fg_of_list ab_Z (3%Z :: nil).

Lemma Zsingle_divides (d : Z) :
  ∀ a, absub_mem (fg_sub (fg_of_list ab_Z (d :: nil))) a → Z.divide d a.
Proof.
  apply (gen_least ab_Z (d :: nil) (Zmultiples d)).
  intros x [Hx | e].
  - assert (d = x) as E by exact Hx.
    rewrite <- E.
    apply Z.divide_refl.
  - destruct e.
Qed.

Lemma Ztwo_proper : absub_mem (fg_sub Ztwo) 1%Z → False.
Proof.
  intro H.
  destruct (Zsingle_divides 2%Z 1%Z H) as [z Hz].
  lia.
Qed.

Lemma Zthree_proper : absub_mem (fg_sub Zthree) 1%Z → False.
Proof.
  intro H.
  destruct (Zsingle_divides 3%Z 1%Z H) as [z Hz].
  lia.
Qed.

(* 相关说明。 （已译） *)

Definition Zjoin : FGObj ab_Z := fg_join Ztwo Zthree.

Example Zjoin_gens : fg_gens Zjoin = (2%Z :: 3%Z :: nil) := eq_refl.

Lemma Zjoin_one : absub_mem (fg_sub Zjoin) 1%Z.
Proof.
  refine (ig_resp (cmon_plus ab_Z 3%Z (ab_neg ab_Z 2%Z)) 1%Z _ _).
  - reflexivity.
  - apply ig_plus.
    + apply ig_gen; simpl; right; left; reflexivity.
    + apply ig_neg; apply ig_gen; simpl; left; reflexivity.
Defined.

(** The two 对象 INCOMPARABLE: neither includes 进入 other, so
 join not just one them disguise. This what makes
 directedness say something here. （已译） *)

Lemma Ztwo_two : absub_mem (fg_sub Ztwo) 2%Z.
Proof. apply ig_gen; simpl; left; reflexivity. Defined.

Lemma Zthree_three : absub_mem (fg_sub Zthree) 3%Z.
Proof. apply ig_gen; simpl; left; reflexivity. Defined.

Lemma Zsub_incomparable :
  (((Ztwo ~{FGSub ab_Z}~> Zthree) → False)
     * ((Zthree ~{FGSub ab_Z}~> Ztwo) → False))%type.
Proof.
  split.
  - intro f.
    destruct (Zsingle_divides 3%Z 2%Z (f 2%Z Ztwo_two)) as [z Hz]; lia.
  - intro f.
    destruct (Zsingle_divides 2%Z 3%Z (f 3%Z Zthree_three)) as [z Hz]; lia.
Qed.

(** 本节：So index really directed non-degenerate way: join
 contains element lies neither. （已译） *)
Lemma Zjoin_strictly_larger :
  (((absub_mem (fg_sub Ztwo) 1%Z → False)
      * (absub_mem (fg_sub Zthree) 1%Z → False))
     * absub_mem (fg_sub Zjoin) 1%Z)%type.
Proof. exact ((Ztwo_proper, Zthree_proper), Zjoin_one). Defined.

(* 相关说明。 （已译） *)

Definition Ztwo_dup : FGObj ab_Z := fg_of_list ab_Z (2%Z :: 2%Z :: nil).

Definition Ztwo_incl_dup : Ztwo ~{FGSub ab_Z}~> Ztwo_dup.
Proof.
  refine (gen_mono ab_Z (2%Z :: nil) (2%Z :: 2%Z :: nil) _).
  intros x [Hx | e].
  - apply ig_gen; simpl; left; exact Hx.
  - destruct e.
Defined.

Definition Ztwo_dup_incl : Ztwo_dup ~{FGSub ab_Z}~> Ztwo.
Proof.
  refine (gen_mono ab_Z (2%Z :: 2%Z :: nil) (2%Z :: nil) _).
  intros x [Hx | [Hx | e]].
  - apply ig_gen; simpl; left; exact Hx.
  - apply ig_gen; simpl; left; exact Hx.
  - destruct e.
Defined.

Definition Ztwo_dup_iso : @Isomorphism (FGSub ab_Z) Ztwo Ztwo_dup := {|
  to          := Ztwo_incl_dup;
  from        := Ztwo_dup_incl;
  iso_to_from := I;
  iso_from_to := I
|}.
