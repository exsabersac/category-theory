(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Construction.Deloop.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Category.Instance.Comp.

Generalizable All Variables.
Open Scope nat_scope.
Section NF.

(* tail t, cycle c (c >= 1) *)
Context (t c : nat).

Definition rho_nf (k : nat) : nat :=
  if k <? t then k else t + (k - t) mod c.

Lemma rho_nf_lt (k : nat) : k < t -> rho_nf k = k.
Proof. intros H. unfold rho_nf. now apply Nat.ltb_lt in H as ->. Qed.

Lemma rho_nf_ge (k : nat) : t <= k -> rho_nf k = t + (k - t) mod c.
Proof.
  intros H. unfold rho_nf.
  destruct (k <? t) eqn:E; [ apply Nat.ltb_lt in E; lia | reflexivity ].
Qed.

Lemma rho_nf_bound (Hc : 0 < c) (k : nat) : rho_nf k < t + c.
Proof.
  unfold rho_nf. destruct (k <? t) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - assert ((k - t) mod c < c) by (apply Nat.mod_upper_bound; lia). lia.
Qed.

Lemma rho_nf_t : rho_nf t = t.
Proof.
  rewrite rho_nf_ge by lia. rewrite Nat.sub_diag, Nat.Div0.mod_0_l. lia.
Qed.

(* The generating 关系 respected: s^(t+c) s^t have one rho_nf. （已译） *)
Lemma rho_nf_rel : rho_nf (t + c) = rho_nf t.
Proof.
  rewrite rho_nf_t, rho_nf_ge by lia.
  replace (t + c - t) with c by lia.
  rewrite Nat.Div0.mod_same. lia.
Qed.

(* Below t + c normal form 恒等. （已译） *)
Lemma rho_nf_small (Hc : 0 < c) (k : nat) : k < t + c -> rho_nf k = k.
Proof.
  intros H. destruct (Nat.ltb_spec k t) as [Hk | Hk].
  - now apply rho_nf_lt.
  - rewrite rho_nf_ge by lia. rewrite Nat.mod_small by lia. lia.
Qed.

(* Above t + c, dropping one cycle leaves the normal form alone. *)
Lemma rho_nf_sub (k : nat) : t + c <= k -> rho_nf (k - c) = rho_nf k.
Proof.
  intros H. rewrite !rho_nf_ge by lia.
  replace (k - t) with ((k - c - t) + c) by lia.
  now rewrite <- Nat.Div0.add_mod_idemp_r, Nat.Div0.mod_same, Nat.add_0_r.
Qed.

Lemma rho_nf_idem (k : nat) : rho_nf (rho_nf k) = rho_nf k.
Proof.
  destruct (Nat.ltb_spec k t) as [H | H].
  - rewrite (rho_nf_lt k H). exact (rho_nf_lt k H).
  - rewrite (rho_nf_ge k H), rho_nf_ge by lia.
    replace (t + (k - t) mod c - t) with ((k - t) mod c) by lia.
    now rewrite Nat.Div0.mod_mod.
Qed.

(* The key absorption law. *)
Lemma rho_nf_add_l (a b : nat) : rho_nf (a + b) = rho_nf (rho_nf a + b).
Proof.
  destruct (Nat.ltb_spec a t) as [Ha | Ha].
  - now rewrite (rho_nf_lt a Ha).
  - rewrite (rho_nf_ge a Ha).
    rewrite !rho_nf_ge by lia.
    replace (t + (a - t) mod c + b - t) with ((a - t) mod c + b) by lia.
    replace (a + b - t) with ((a - t) + b) by lia.
    now rewrite Nat.Div0.add_mod_idemp_l.
Qed.

Lemma rho_nf_add (a b : nat) : rho_nf (a + b) = rho_nf (rho_nf a + rho_nf b).
Proof.
  rewrite rho_nf_add_l.
  rewrite (Nat.add_comm (rho_nf a) b), rho_nf_add_l, Nat.add_comm.
  reflexivity.
Qed.

End NF.
Close Scope nat_scope.

Open Scope category_scope.




Definition OneGen : Quiver := OneNodeQuiver unit.

Fixpoint spath (k : nat) : ttt ~{FreeOnQuiver OneGen}~> ttt :=
  match k with
  | O   => tnil
  | S j => tcons (B:=@edges OneGen) _ tt (spath j)
  end.

(* The same path, at variable endpoints -- [poly_unit] has one element. *)
Definition spath_at (x y : OneGen) (k : nat) :
  x ~{FreeOnQuiver OneGen}~> y :=
  match x as x', y as y' return (x' ~{FreeOnQuiver OneGen}~> y') with
  | ttt, ttt => spath k
  end.

Example spath_at_ttt (k : nat) : spath_at ttt ttt k = spath k := eq_refl.

(* One node, one edge, carried as data in the shape Presented.v fixes. *)
Definition OneGenFinite : FiniteQuiver OneGen.
Proof.
  unshelve refine {| fq_nodes := 1%nat; fq_edges := fun _ _ => 1%nat |}.
  - exact (fun _ => ttt).
  - exact (fun _ => Fin.F1).
  - exact (fun _ _ _ => tt).
  - exact (fun _ _ _ => Fin.F1).
  - intro x; now destruct x.
  - intros x y e; now destruct e.
Defined.


Lemma spath_length (k : nat) : tlist_length (spath k) = k.
Proof. induction k; simpl; auto. Qed.

Lemma spath_at_length (x y : OneGen) (k : nat) :
  tlist_length (spath_at x y k) = k.
Proof. destruct x, y; simpl; apply spath_length. Qed.

(* 相关说明。 （已译） *)
Definition sp_spec (j i : OneGen) (p : i ~{FreeOnQuiver OneGen}~> j) : Prop :=
  match i, j return (i ~{FreeOnQuiver OneGen}~> j) -> Prop with
  | ttt, ttt => fun q => q = spath (tlist_length q)
  end p.

Theorem spath_classify (j i : OneGen) (p : i ~{FreeOnQuiver OneGen}~> j) :
  sp_spec j i p.
Proof.
  induction p as [ | a b e p IH ].
  - destruct j; reflexivity.
  - destruct a, b, e, j; unfold sp_spec in *; simpl in *.
    now rewrite <- IH.
Qed.

(* 相关说明。 （已译） *)
Corollary spath_complete (p : ttt ~{FreeOnQuiver OneGen}~> ttt) :
  p = spath (tlist_length p).
Proof. exact (spath_classify ttt ttt p). Qed.

Lemma spath_app (i j : nat) :
  tlist_app (spath i) (spath j) = spath (i + j).
Proof.
  induction i.
  - apply tlist_app_tnil_l.
  - change (spath (S i)) with (tcons (B:=@edges OneGen) ttt tt (spath i)).
    now rewrite <- tlist_app_comm_cons, IHi.
Qed.

(* Composition in [FreeOnQuiver] is [g +++ f], so [spath] adds. *)
Lemma spath_compose (i j : nat) :
  (spath i ∘ spath j)%morphism = spath (j + i).
Proof. exact (spath_app j i). Qed.

(* [Construction/Free/Quiver.v]'s [tlist'_equiv_lengths] gives this in one
   line, which is what [Instance/Square.v]'s [wsq_equiv_length] and
   [Instance/WalkingIso.v]'s [wi_equiv_length] both do; a first draft here
   re-proved it by induction through [fixpoint_implies_inductive]. *)
Lemma free_equiv_length {i j : OneGen}
  (f g : i ~{FreeOnQuiver OneGen}~> j) :
  f ≈ g -> tlist_length f = tlist_length g.
Proof. intro H; exact (tlist'_equiv_lengths _ _ _ _ _ _ _ H). Qed.

Section OneGenPres.
Context (t c : nat).

Definition SEqns : FiniteEquations OneGen.
Proof using c t.
  unshelve refine {| fe_count := fun _ _ => 1%nat |}.
  - exact (fun x y _ => spath_at x y (t + c)).
  - exact (fun x y _ => spath_at x y t).
Defined.

Definition SPres : FinitePresentation :=
  {| fp_quiver := OneGen; fp_finite := OneGenFinite; fp_eqns := SEqns |}.

Definition SCat : Category := FinitelyPresented SPres.

End OneGenPres.


Section OneGenSound.
Context (t c : nat).

Notation SR := (fe_rel OneGen (SEqns t c)).

(* [≈] presented 范畴 IS congruence closure, the
 定义 [Quotient] -- recorded so 定理 below visibly
 about 范畴 not about lookalike. （已译） *)
Example scat_equiv_is_closure (x y : OneGen)
  (f g : x ~{FreeOnQuiver OneGen}~> y) :
  (@equiv _ (@homset (SCat t c) x y) f g)
    = Quotient.CongClosure (fe_rel (SEqns t c)) x y f g := eq_refl.

Theorem rho_sound (x y : OneGen) (f g : x ~{FreeOnQuiver OneGen}~> y)
  (H : Quotient.CongClosure (fe_rel (SEqns t c)) x y f g) :
  rho_nf t c (tlist_length f) = rho_nf t c (tlist_length g).
Proof using .
  induction H as
    [ x y f g Hr | x y f g He | | | x y z f f' g g' H1 IH1 H2 IH2 ].
  - destruct Hr as [i [Hf Hg]].
    rewrite (free_equiv_length _ _ Hf), (free_equiv_length _ _ Hg).
    simpl fe_lhs; simpl fe_rhs.
    rewrite !spath_at_length.
    apply rho_nf_rel.
  - now rewrite (free_equiv_length _ _ He).
  - now symmetry.
  - etransitivity; eassumption.
  - assert (Hl : forall (a b d : OneGen)
                   (u : b ~{FreeOnQuiver OneGen}~> d)
                   (v : a ~{FreeOnQuiver OneGen}~> b),
             tlist_length (u ∘ v) = (tlist_length v + tlist_length u)%nat)
      by (intros; apply tlist_app_length).
    rewrite !Hl.
    rewrite (rho_nf_add t c (tlist_length g) (tlist_length f)),
            (rho_nf_add t c (tlist_length g') (tlist_length f')).
    now rewrite IH1, IH2.
Qed.

End OneGenSound.

(* ------------------------------------------------------------------ *)
(* Completeness: every word reduces to its normal form.                *)
(* ------------------------------------------------------------------ *)

Section OneGenComplete.
Context (t c : nat).

Notation SEq := (@equiv _ (@homset (SCat t c) ttt ttt)).

(* The generating 关系, equation presented 范畴. （已译） *)
Lemma spath_rel : SEq (spath (t + c)) (spath t).
Proof using .
  apply (Quotient.cc_gen (R:=fe_rel (SEqns t c))).
  exists Fin.F1. split; simpl; reflexivity.
Qed.

Lemma spath_refl (k : nat) : SEq (spath k) (spath k).
Proof using . apply Quotient.cc_equiv. reflexivity. Qed.

(* Precomposing 关系 s^a. （已译） *)
Lemma step_down (a : nat) : SEq (spath (a + (t + c))) (spath (a + t)).
Proof using .
  assert (H : SEq (spath (t + c) ∘ spath a) (spath t ∘ spath a))
    by (apply Quotient.cc_comp; [ exact spath_rel | apply spath_refl ]).
  now rewrite !spath_compose in H.
Qed.

End OneGenComplete.

Section OneGenCompleteMain.
Context (t c : nat) (Hc : (0 < c)%nat).
Local Open Scope nat_scope.

Notation SEq := (@equiv _ (@homset (SCat t c) ttt ttt)).

Theorem spath_nf (k : nat) : SEq (spath k) (spath (rho_nf t c k)).
Proof using Hc.
  induction k as [k IH] using (well_founded_induction_type Wf_nat.lt_wf).
  destruct (Nat.ltb k (t + c)) eqn:Hb.
  - apply Nat.ltb_lt in Hb.
    rewrite (rho_nf_small t c Hc k Hb). apply spath_refl.
  - apply Nat.ltb_ge in Hb. rename Hb into Hk.
    assert (Hstep : SEq (spath k) (spath (k - c))).
    { replace k with ((k - (t + c)) + (t + c)) at 1 by lia.
      replace (k - c) with ((k - (t + c)) + t) by lia.
      apply step_down. }
    apply (Quotient.cc_trans Hstep).
    rewrite <- (rho_nf_sub t c k Hk).
    apply IH. lia.
Qed.

(* The two directions, named separately: a consumer usually wants one. *)
Lemma rho_nf_of_spath_eq (i j : nat) :
  SEq (spath i) (spath j) -> rho_nf t c i = rho_nf t c j.
Proof using .
  intro H.
  pose proof (rho_sound t c ttt ttt (spath i) (spath j) H) as Hs.
  now rewrite !spath_length in Hs.
Qed.

Lemma spath_eq_of_rho_nf (i j : nat) :
  rho_nf t c i = rho_nf t c j -> SEq (spath i) (spath j).
Proof using Hc.
  intro H.
  apply (Quotient.cc_trans (spath_nf i)).
  rewrite H.
  apply Quotient.cc_sym, spath_nf.
Qed.

(* THE DECISION PROCEDURE: two words equal presented 范畴
 exactly normal forms agree. （已译） *)
Theorem spath_iff (i j : nat) :
  SEq (spath i) (spath j) ↔ rho_nf t c i = rho_nf t c j.
Proof using Hc.
  split; [ apply rho_nf_of_spath_eq | apply spath_eq_of_rho_nf ].
Qed.

(* 相关说明。 （已译） *)
Lemma spath_distinct (i j : nat) :
  i < t + c -> j < t + c -> SEq (spath i) (spath j) -> i = j.
Proof using Hc.
  intros Hi Hj H. apply spath_iff in H.
  rewrite (rho_nf_small t c Hc i Hi), (rho_nf_small t c Hc j Hj) in H. exact H.
Qed.

(* 相关说明。 （已译） *)
Lemma spath_exhaust (k : nat) :
  { r : nat & ((r < t + c) * SEq (spath k) (spath r))%type }.
Proof using Hc.
  exists (rho_nf t c k). split.
  - apply rho_nf_bound; exact Hc.
  - apply spath_nf.
Qed.

(* Every arrow presented 范畴 one [t + c] words. （已译） *)
Lemma scat_arrow_normal (p : ttt ~{SCat t c}~> ttt) :
  { r : nat & ((r < t + c) * SEq p (spath r))%type }.
Proof using Hc.
  destruct (spath_exhaust (tlist_length p)) as [r [Hr Heq]].
  exists r. split; [ exact Hr | ].
  refine (Quotient.cc_trans _ Heq).
  apply Quotient.cc_equiv.
  rewrite <- (spath_complete p) at 1. reflexivity.
Qed.

End OneGenCompleteMain.

(* ================================================================== *)
(*  The four examples.  Each is [SCat] at two numbers, so nothing      *)
(*  below re-proves any of the theory above.                           *)
(* ================================================================== *)

Definition SEqAt (t c : nat)
  (p q : ttt ~{FreeOnQuiver OneGen}~> ttt) : Type :=
  @equiv _ (@homset (SCat t c) ttt ttt) p q.

(* 相关说明。 （已译） *)

Definition Z2Cat : Category := SCat 0 2.

Lemma z2_rel : SEqAt 0 2 (spath 2) (spath 0).
Proof. apply spath_eq_of_rho_nf; [ lia | reflexivity ]. Qed.

(* Seven Sketches §3.2.2's point: imposing ONE equation forces others. *)
Lemma z2_cube : SEqAt 0 2 (spath 3) (spath 1).
Proof. apply spath_eq_of_rho_nf; [ lia | reflexivity ]. Qed.

Lemma z2_fourth : SEqAt 0 2 (spath 4) (spath 0).
Proof. apply spath_eq_of_rho_nf; [ lia | reflexivity ]. Qed.

(* ...and collapse: exactly two 态射, [id] [s]. （已译） *)
Lemma z2_distinct : SEqAt 0 2 (spath 0) (spath 1) -> False.
Proof.
  intro H. apply (rho_nf_of_spath_eq 0 2) in H. discriminate.
Qed.

Lemma z2_exhaust (p : ttt ~{Z2Cat}~> ttt) :
  { r : nat & ((r < 2)%nat * SEqAt 0 2 p (spath r))%type }.
Proof. apply (scat_arrow_normal 0 2 ltac:(lia)). Qed.

(* * ** (b) The two-element idempotent 幺半群 -- Awodey's [f∘f = f] （已译） *)

Definition IdemCat : Category := SCat 1 1.

Lemma idem_rel : SEqAt 1 1 (spath 2) (spath 1).
Proof. apply spath_eq_of_rho_nf; [ lia | reflexivity ]. Qed.

Lemma idem_distinct : SEqAt 1 1 (spath 0) (spath 1) -> False.
Proof.
  intro H. apply (rho_nf_of_spath_eq 1 1) in H. discriminate.
Qed.

Lemma idem_exhaust (p : ttt ~{IdemCat}~> ttt) :
  { r : nat & ((r < 2)%nat * SEqAt 1 1 p (spath r))%type }.
Proof. apply (scat_arrow_normal 1 1 ltac:(lia)). Qed.

(* 相关说明。 （已译） *)

Definition CycCat (n : nat) : Category := SCat 0 n.

Lemma cyc_rel (n : nat) : (0 < n)%nat -> SEqAt 0 n (spath n) (spath 0).
Proof.
  intro Hn. apply spath_eq_of_rho_nf; [ exact Hn | ].
  rewrite (rho_nf_t 0 n). rewrite rho_nf_ge by lia.
  rewrite Nat.sub_0_r, Nat.Div0.mod_same. reflexivity.
Qed.

Lemma cyc_exhaust (n : nat) (Hn : (0 < n)%nat)
  (p : ttt ~{CycCat n}~> ttt) :
  { r : nat & ((r < 0 + n)%nat * SEqAt 0 n p (spath r))%type }.
Proof. apply (scat_arrow_normal 0 n Hn). Qed.

(* 相关说明。 （已译） *)

Definition TailCat : Category := SCat 2 3.

Lemma tail_rel : SEqAt 2 3 (spath 5) (spath 2).
Proof. apply spath_eq_of_rho_nf; [ lia | reflexivity ]. Qed.

Lemma tail_exhaust (p : ttt ~{TailCat}~> ttt) :
  { r : nat & ((r < 5)%nat * SEqAt 2 3 p (spath r))%type }.
Proof. apply (scat_arrow_normal 2 3 ltac:(lia)). Qed.

(* 相关说明。 （已译） *)
Lemma tail_distinct (i j : nat) :
  (i < 5)%nat -> (j < 5)%nat -> SEqAt 2 3 (spath i) (spath j) -> i = j.
Proof. apply (spath_distinct 2 3 ltac:(lia)). Qed.

(* 相关说明。 （已译） *)
Lemma tail_not_group (k : nat) :
  SEqAt 2 3 (spath 1 ∘ spath k)%morphism (spath 0) -> False.
Proof.
  intro H. rewrite spath_compose in H.
  apply (rho_nf_of_spath_eq 2 3) in H.
  rewrite (rho_nf_lt 2 3 0 ltac:(lia)) in H.
  destruct k as [| k']; simpl in H.
  - rewrite (rho_nf_lt 2 3 1 ltac:(lia)) in H. discriminate.
  - rewrite (rho_nf_ge 2 3 (S (k' + 1)) ltac:(lia)) in H. lia.
Qed.

(* ================================================================== *)
(*  Z/2Z, related to the group already in tree.                        *)
(*                                                                     *)
(* 相关说明。 （已译） *)
(*  construction not be left as two unconnected objects.                *)
(*  [Instance/Comp.v]'s [UniversalAlgebra.Bool : Group] is that     *)
(* 对象: booleans under [xor], algebra group （已译） *)
(*  signature.  Its underlying [OpAlgebra] is [BoolOp].          *)
(*                                                                     *)
(*  AXIOM DISCLOSURE, MEASURED rather than assumed: [BoolOp] and [xor]  *)
(* 相关说明。 （已译） *)
(* carries [functional_extensionality_dep] -- it 证明 the （已译） *)
(*  group EQUATIONS that spends it, in a module whose header already    *)
(* 相关说明。 （已译） *)
(*  [BoolOp], which costs nothing; anything mentioning [Bool] would     *)
(* inherit axiom, file states no such 常值. The （已译） *)
(*  requirement costs the closure exactly TWO modules (34 -> 36).       *)
(* ================================================================== *)

(* The parity of a word, as an element of [bool]. *)
Definition z2_bool (p : ttt ~{FreeOnQuiver OneGen}~> ttt) : bool :=
  Nat.eqb (rho_nf 0 2 (tlist_length p)) 1.

(* It well defined presented 范畴 -- soundness IS this. （已译） *)
Lemma z2_bool_respects (p q : ttt ~{FreeOnQuiver OneGen}~> ttt) :
  SEqAt 0 2 p q -> z2_bool p = z2_bool q.
Proof.
  intro H. unfold z2_bool.
  pose proof (rho_sound 0 2 ttt ttt p q H) as Hs. now rewrite Hs.
Qed.

Example z2_bool_id : z2_bool (spath 0) = false := eq_refl.
Example z2_bool_gen : z2_bool (spath 1) = true := eq_refl.

(* The rho_nf value is always 0 or 1, which is what makes parity total. *)
Lemma z2_rho_nf_binary (k : nat) :
  rho_nf 0 2 k = 0%nat \/ rho_nf 0 2 k = 1%nat.
Proof.
  pose proof (rho_nf_bound 0 2 ltac:(lia) k) as Hb.
  destruct (rho_nf 0 2 k) as [| [| n]]; [ now left | now right | ]. lia.
Qed.

(* Composition goes [xor] -- so presented 幺半群 IS boolean
 one, [xor] here [BoolOp]'s own multiplication. （已译） *)
Lemma z2_bool_compose (p q : ttt ~{FreeOnQuiver OneGen}~> ttt) :
  z2_bool (p ∘ q)%morphism
    = UniversalAlgebra.xor (z2_bool p) (z2_bool q).
Proof.
  unfold z2_bool.
  assert (Hl : tlist_length (p ∘ q)%morphism
                 = (tlist_length q + tlist_length p)%nat)
    by apply tlist_app_length.
  rewrite Hl, (rho_nf_add 0 2 (tlist_length q) (tlist_length p)).
  destruct (z2_rho_nf_binary (tlist_length q)) as [Hq | Hq];
  destruct (z2_rho_nf_binary (tlist_length p)) as [Hp | Hp];
    rewrite Hq, Hp; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Example boolop_mul
  (args : @UniversalAlgebra.arity UniversalAlgebra.GroupOp
            UniversalAlgebra.mul -> bool) :
  UniversalAlgebra.op UniversalAlgebra.BoolOp UniversalAlgebra.mul args
    = UniversalAlgebra.xor (args UniversalAlgebra.Fst)
                           (args UniversalAlgebra.Snd) := eq_refl.

Example boolop_one
  (args : @UniversalAlgebra.arity UniversalAlgebra.GroupOp
            UniversalAlgebra.one -> bool) :
  UniversalAlgebra.op UniversalAlgebra.BoolOp UniversalAlgebra.one args
    = false := eq_refl.

(* ================================================================== *)
(*  The one-object reading, in Presented.v's own monoid vocabulary.    *)
(* 相关说明。 （已译） *)
(* 相关说明。 （已译） *)
(* ================================================================== *)

Definition RhoMon (t c : nat) : MonObject :=
  PresentedMonoidOn unit (fe_rel (SEqns t c)).

Example smon_is_hom_monoid (t c : nat) :
  RhoMon t c = hom_monoid (SCat t c) ttt := eq_refl.

(* ...and FREE one-generator 幺半群 free 范畴's hom
 幺半群, [spath_complete] identifies (nat, +, 0). （已译） *)
Example free_mon_is_hom_monoid :
  FreeMonoidOn unit = hom_monoid (FreeOnQuiver OneGen) ttt := eq_refl.
