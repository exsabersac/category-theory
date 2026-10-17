Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Graded monads *)

(*
 nLab: https://ncatlab.org/nlab/show/graded+monad

   本文件给出单子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record GradeMonoid : Type := {
  grade :> Type;                        (* the underlying type of grades *)
  gunit : grade;                        (* the neutral grade ε *)
  gmul : grade → grade → grade;         (* grade composition m · n *)

  gmul_assoc {a b c : grade} : gmul (gmul a b) c = gmul a (gmul b c);
  gmul_unit_l {a : grade} : gmul gunit a = a;
  gmul_unit_r {a : grade} : gmul a gunit = a
}.

Section Graded.

Context {C : Category}.
Context {E : GradeMonoid}.
Context {T : E → C ⟶ C}.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition gcast {m n : E} (e : m = n) {x : C} : T m x ~> T n x :=
  match e in _ = k return T m x ~> T k x with
  | eq_refl => id
  end.

Lemma gcast_refl {m : E} {x : C} : @gcast m m eq_refl x ≈ id.
Proof. reflexivity. Qed.

Lemma gcast_trans {m n p : E} (e1 : m = n) (e2 : n = p) {x : C} :
  gcast e2 ∘ @gcast m n e1 x ≈ gcast (eq_trans e1 e2).
Proof. destruct e2, e1; simpl; cat. Qed.

(* [gcast] is natural in the object variable: it commutes with the functorial
   action of the graded carriers. *)
Lemma gcast_natural {m n : E} (e : m = n) {x y : C} (f : x ~> y) :
  gcast e ∘ fmap[T m] f ≈ fmap[T n] f ∘ @gcast m n e x.
Proof. destruct e; simpl; cat. Qed.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class GradedMonad := {
  gret {x : C} : x ~> T (gunit E) x;                       (* graded unit η *)
  gjoin {m n : E} {x : C} : T m (T n x) ~> T (gmul E m n) x;   (* graded μ *)

  (* naturality of the unit η: gret ∘ f ≈ fmap f ∘ gret *)
  gfmap_ret {x y : C} (f : x ~> y) :
    gret ∘ f ≈ fmap[T (gunit E)] f ∘ gret;

  (* graded associativity: μ ∘ Tμ ≈ μ ∘ μT, up to gmul_assoc *)
  gjoin_fmap_join {m n p : E} {x : C} :
    gjoin ∘ fmap[T m] (@gjoin n p x)
      ≈ gcast (gmul_assoc E) ∘ @gjoin (gmul E m n) p x ∘ @gjoin m n (T p x);

  (* graded left unit law: μ ∘ Tη ≈ id, up to gmul_unit_r *)
  gjoin_fmap_ret {m : E} {x : C} :
    gjoin ∘ fmap[T m] (@gret x) ≈ gcast (eq_sym (gmul_unit_r E));

  (* graded right unit law: μ ∘ ηT ≈ id, up to gmul_unit_l *)
  gjoin_ret {m : E} {x : C} :
    gjoin ∘ @gret (T m x) ≈ gcast (eq_sym (gmul_unit_l E));

  (* naturality of the multiplication μ *)
  gjoin_fmap_fmap {m n : E} {x y : C} (f : x ~> y) :
    gjoin ∘ fmap[T m] (fmap[T n] f) ≈ fmap[T (gmul E m n)] f ∘ gjoin
}.

End Graded.

Arguments GradedMonad {C} E T.

(* Over a constant family the cast is always the identity, whatever the grade
   equation was: the transport happens in a family that does not move. *)
Lemma gcast_const {C : Category} {E : GradeMonoid} {M : C ⟶ C}
      {m n : E} (e : m = n) {x : C} :
  @gcast C E (fun _ => M) m n e x ≈ id.
Proof. destruct e; reflexivity. Qed.

(** ** The degenerate-grading bridge *)

(* The one-element grade monoid.  All three law proofs are transparent
   match-terms reducing to [eq_refl] on [ttt], so at this grading [gcast]
   is definitionally [id]. *)
Definition Trivial_GradeMonoid : GradeMonoid := {|
  grade := poly_unit;
  gunit := ttt;
  gmul := fun _ _ => ttt;
  gmul_assoc := fun _ _ _ => eq_refl;
  gmul_unit_l := fun a => match a as u return ttt = u with ttt => eq_refl end;
  gmul_unit_r := fun a => match a as u return ttt = u with ttt => eq_refl end
|}.

#[local] Obligation Tactic := idtac.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition GradedMonad_Monad {C : Category} {M : C ⟶ C}
  (G : @GradedMonad C Trivial_GradeMonoid (fun _ => M)) : @Monad C M := {|
  ret  := fun x => @gret C Trivial_GradeMonoid (fun _ => M) G x;
  join := fun x => @gjoin C Trivial_GradeMonoid (fun _ => M) G ttt ttt x
|}.
Next Obligation. (* fmap_ret *)
  intros C M G x y f.
  exact (@gfmap_ret C Trivial_GradeMonoid (fun _ => M) G x y f).
Qed.
Next Obligation. (* join_fmap_join *)
  intros C M G x.
  etransitivity.
  - exact (@gjoin_fmap_join C Trivial_GradeMonoid (fun _ => M) G ttt ttt ttt x).
  - rewrite gcast_const; cat.
Qed.
Next Obligation. (* join_fmap_ret: the cast is definitionally [id] here *)
  intros C M G x.
  exact (@gjoin_fmap_ret C Trivial_GradeMonoid (fun _ => M) G ttt x).
Qed.
Next Obligation. (* join_ret: the cast is definitionally [id] here *)
  intros C M G x.
  exact (@gjoin_ret C Trivial_GradeMonoid (fun _ => M) G ttt x).
Qed.
Next Obligation. (* join_fmap_fmap *)
  intros C M G x y f.
  exact (@gjoin_fmap_fmap C Trivial_GradeMonoid (fun _ => M) G ttt ttt x y f).
Qed.

(*
   本节说明单子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Monad_GradedMonad_const {C : Category} {M : C ⟶ C}
  (H : @Monad C M) (E : GradeMonoid) : @GradedMonad C E (fun _ => M) := {|
  gret  := fun x => @ret C M H x;
  gjoin := fun _ _ x => @join C M H x
|}.
Next Obligation. (* gfmap_ret *)
  intros C M H E x y f.
  exact (@fmap_ret C M H x y f).
Qed.
Next Obligation. (* gjoin_fmap_join *)
  intros C M H E m n p x.
  rewrite gcast_const, id_left.
  exact (@join_fmap_join C M H x).
Qed.
Next Obligation. (* gjoin_fmap_ret *)
  intros C M H E m x.
  rewrite gcast_const.
  exact (@join_fmap_ret C M H x).
Qed.
Next Obligation. (* gjoin_ret *)
  intros C M H E m x.
  rewrite gcast_const.
  exact (@join_ret C M H x).
Qed.
Next Obligation. (* gjoin_fmap_fmap *)
  intros C M H E m n x y f.
  exact (@join_fmap_fmap C M H x y f).
Qed.

(* Round-trips at the trivial grading hold definitionally: passing through
   either bridge leaves the structure maps unchanged. *)

Corollary roundtrip_ret {C : Category} {M : C ⟶ C} (H : @Monad C M) (x : C) :
  @gret C Trivial_GradeMonoid (fun _ => M)
        (Monad_GradedMonad_const H Trivial_GradeMonoid) x ≈ @ret C M H x.
Proof. reflexivity. Qed.

Corollary roundtrip_join {C : Category} {M : C ⟶ C}
  (G : @GradedMonad C Trivial_GradeMonoid (fun _ => M)) (x : C) :
  @join C M (GradedMonad_Monad G) x
    ≈ @gjoin C Trivial_GradeMonoid (fun _ => M) G ttt ttt x.
Proof. reflexivity. Qed.

Corollary roundtrip_ret_trivial {C : Category} {M : C ⟶ C}
  (G : @GradedMonad C Trivial_GradeMonoid (fun _ => M)) (x : C) :
  @ret C M (GradedMonad_Monad G) x
    ≈ @gret C Trivial_GradeMonoid (fun _ => M) G x.
Proof. reflexivity. Qed.

Corollary roundtrip_join_const {C : Category} {M : C ⟶ C}
  (H : @Monad C M) (x : C) :
  @gjoin C Trivial_GradeMonoid (fun _ => M)
         (Monad_GradedMonad_const H Trivial_GradeMonoid) ttt ttt x
    ≈ @join C M H x.
Proof. reflexivity. Qed.

(** ** A nontrivial instance: the bool-graded exception monad over Coq *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AndGrade : GradeMonoid := {|
  grade := bool;
  gunit := true;
  gmul := andb;
  gmul_assoc := fun a b c =>
    match a as a0 return andb (andb a0 b) c = andb a0 (andb b c) with
    | true  => eq_refl
    | false => eq_refl
    end;
  gmul_unit_l := fun a => eq_refl;
  gmul_unit_r := fun a =>
    match a as a0 return andb a0 true = a0 with
    | true  => eq_refl
    | false => eq_refl
    end
|}.

(* The option endofunctor on Coq, defined locally as a categorical functor
   (Theory/Coq covers the programming-style classes instead). *)
Program Definition option_Functor : Coq ⟶ Coq := {|
  fobj := option;
  fmap := fun _ _ f o => option_map f o
|}.
Next Obligation. (* fmap_respects *)
  intros x y f g Hfg [a|]; simpl; [rewrite Hfg|]; reflexivity.
Qed.
Next Obligation. (* fmap_id *)
  intros x [a|]; reflexivity.
Qed.
Next Obligation. (* fmap_comp *)
  intros x y z f g [a|]; reflexivity.
Qed.

(* The graded carrier: at the pure grade the identity functor, at the
   impure grade [option]. *)
Definition ExcT (b : bool) : Coq ⟶ Coq :=
  if b then Id[Coq] else option_Functor.

(* The graded unit lives at grade [true], where the carrier is [Id]. *)
Definition exc_ret (x : Type) : x → ExcT true x := fun a => a.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition exc_join (b1 b2 : bool) (x : Type) :
  ExcT b1 (ExcT b2 x) → ExcT (andb b1 b2) x :=
  match b1 as a, b2 as b return ExcT a (ExcT b x) → ExcT (andb a b) x with
  | true, _      => fun o => o
  | false, true  => fun o => o
  | false, false => fun o => match o with
                             | Some v => v
                             | None   => None
                             end
  end.

(*
   本节说明 Graded 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Exc_GradedMonad : @GradedMonad Coq AndGrade ExcT := {|
  gret  := exc_ret;
  gjoin := exc_join
|}.
Next Obligation. (* gfmap_ret *)
  intros x y f a; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_join *)
  intros m n p x; destruct m, n, p; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_ret *)
  intros m x; destruct m; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.
Next Obligation. (* gjoin_ret *)
  intros m x; destruct m; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_fmap *)
  intros m n x y f; destruct m, n; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.

(** ** The grade-only writer *)

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition GradedWriter (W : GradeMonoid) :
  @GradedMonad Coq W (fun _ => Id[Coq]) := {|
  gret  := fun x (a : x) => a;
  gjoin := fun _ _ x (a : x) => a
|}.
Next Obligation. (* gfmap_ret *)
  intros W x y f; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_join *)
  intros W m n p x; rewrite gcast_const; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_ret *)
  intros W m x; rewrite gcast_const; reflexivity.
Qed.
Next Obligation. (* gjoin_ret *)
  intros W m x; rewrite gcast_const; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_fmap *)
  intros W m n x y f; reflexivity.
Qed.
