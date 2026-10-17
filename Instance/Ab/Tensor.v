(* 相关说明。 （已译） *)

(*
 Book:      Mac Lane, ibid., §VII.1, printed pp. 163–164 (PDF pp.
 nLab:      https://ncatlab.org/nlab/show/tensor+product+of+abelian+groups
 Wikipedia: https://en.wikipedia.org/wiki/Tensor_product

   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

Section Tensor.

Context (G H : AbObject).

(* Formal sums over the two carriers: generators, zero, sum, negation. *)
Inductive tsum : Type :=
  | ts_gen  : carrier G → carrier H → tsum
  | ts_zero : tsum
  | ts_plus : tsum → tsum → tsum
  | ts_neg  : tsum → tsum.

(* The quotienting relation: commutative-group laws, bilinearity each
 variable, congruence, saturation under point setoids, symmetry and
 transitivity. Reflexivity is derived (design 注 1).（已译） *)
Inductive ts_eq : tsum → tsum → Prop :=
  | te_gen {g g' : carrier G} {h h' : carrier H} :
      g ≈ g' → h ≈ h' → ts_eq (ts_gen g h) (ts_gen g' h')
  | te_plus {s s' t t'} :
      ts_eq s s' → ts_eq t t' → ts_eq (ts_plus s t) (ts_plus s' t')
  | te_neg {s s'} : ts_eq s s' → ts_eq (ts_neg s) (ts_neg s')
  | te_assoc (s t u : tsum) :
      ts_eq (ts_plus (ts_plus s t) u) (ts_plus s (ts_plus t u))
  | te_comm (s t : tsum) : ts_eq (ts_plus s t) (ts_plus t s)
  | te_zero_l (s : tsum) : ts_eq (ts_plus ts_zero s) s
  | te_neg_l (s : tsum) : ts_eq (ts_plus (ts_neg s) s) ts_zero
  | te_bilin_l (g g' : carrier G) (h : carrier H) :
      ts_eq (ts_gen (cmon_plus G g g') h)
            (ts_plus (ts_gen g h) (ts_gen g' h))
  | te_bilin_r (g : carrier G) (h h' : carrier H) :
      ts_eq (ts_gen g (cmon_plus H h h'))
            (ts_plus (ts_gen g h) (ts_gen g h'))
  | te_sym {s t} : ts_eq s t → ts_eq t s
  | te_trans {s t u} : ts_eq s t → ts_eq t u → ts_eq s u.

Lemma ts_refl (s : tsum) : ts_eq s s.
Proof.
  induction s.
  - exact (te_gen (reflexivity _) (reflexivity _)).
  - exact (te_trans (te_sym (te_zero_l ts_zero)) (te_zero_l ts_zero)).
  - exact (te_plus IHs1 IHs2).
  - exact (te_neg IHs).
Qed.

Lemma ts_eq_Equivalence : Equivalence ts_eq.
Proof.
  constructor.
  - exact ts_refl.
  - exact (fun s t => te_sym).
  - exact (fun s t u => te_trans).
Qed.

Definition ts_Setoid : Setoid tsum := {|
  equiv        := ts_eq;
  setoid_equiv := ts_eq_Equivalence
|}.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AbTensor : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := tsum; is_setoid := ts_Setoid |};
    cmon_zero := ts_zero;
    cmon_plus := ts_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => te_plus Hs Ht;
    cmon_plus_assoc := te_assoc;
    cmon_plus_comm := te_comm;
    cmon_plus_zero_l := te_zero_l;
    (* [ts_eq] IS [Prop]-valued 关系, so it own [Prop] 镜像 and
 both 蕴含 恒等. （已译） *)
    cmon_prop := @PropEquiv_of_relation _ ts_Setoid ts_eq
                   (fun _ _ h => h) (fun _ _ h => h)
  |};
  ab_neg := ts_neg;
  ab_neg_respects := fun _ _ Hs => te_neg Hs;
  ab_neg_left := te_neg_l
|}.

(* * ** Bilinear maps 普遍性质 （已译） *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record Bilinear (K : AbObject) := {
  bilin_map : carrier G → carrier H → carrier K;
  bilin_respects :
    Proper (equiv ==> equiv ==> equiv) bilin_map;
  bilin_add_l (g g' : carrier G) (h : carrier H) :
    bilin_map (cmon_plus G g g') h
      ≈ cmon_plus K (bilin_map g h) (bilin_map g' h);
  bilin_add_r (g : carrier G) (h h' : carrier H) :
    bilin_map g (cmon_plus H h h')
      ≈ cmon_plus K (bilin_map g h) (bilin_map g h')
}.

Arguments bilin_map {K} _ _ _.
Arguments bilin_respects {K} _.
Arguments bilin_add_l {K} _ _ _ _.
Arguments bilin_add_r {K} _ _ _ _.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tensor_gen : Bilinear AbTensor :=
  @Build_Bilinear AbTensor ts_gen
    (fun _ _ Hg _ _ Hh => te_gen Hg Hh)
    te_bilin_l
    te_bilin_r.

(* 相关说明。 （已译） *)
Fixpoint tensor_med_fun {K : AbObject} (β : Bilinear K) (s : tsum) :
  carrier K :=
  match s with
  | ts_gen g h  => bilin_map β g h
  | ts_zero     => cmon_zero K
  | ts_plus s t => cmon_plus K (tensor_med_fun β s) (tensor_med_fun β t)
  | ts_neg s    => ab_neg K (tensor_med_fun β s)
  end.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tensor_med_respects {K : AbObject} (β : Bilinear K) (s t : tsum) :
  ts_eq s t → tensor_med_fun β s ≈ tensor_med_fun β t.
Proof.
  intro He.
  apply pequiv_to.
  induction He as
    [ g g' h h' Hg Hh | s s' t t' _ IH1 _ IH2 | s s' _ IH
    | s t u | s t | s | s | g g' h | g h h'
    | s t _ IH | s t u _ IH1 _ IH2 ]; simpl.
  - apply pequiv_from; exact (bilin_respects β _ _ Hg _ _ Hh).
  - apply pequiv_from.
    exact (cmon_plus_respects K _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from.
    exact (ab_neg_respects K _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from; exact (cmon_plus_assoc K _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm K _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l K _).
  - apply pequiv_from; exact (ab_neg_left K _).
  - apply pequiv_from; exact (bilin_add_l β _ _ _).
  - apply pequiv_from; exact (bilin_add_r β _ _ _).
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

(* 相关说明。 （已译） *)
Program Definition tensor_ump {K : AbObject} (β : Bilinear K) :
  AbHom AbTensor K := {|
  cmon_map := {| morphism := tensor_med_fun β |}
|}.
Next Obligation.
  intros K β s t He; exact (tensor_med_respects β s t He).
Qed.
Next Obligation.
  intros K β; simpl; reflexivity.
Qed.
Next Obligation.
  intros K β s t; simpl; reflexivity.
Qed.

Lemma tensor_ump_gen {K : AbObject} (β : Bilinear K)
  (g : carrier G) (h : carrier H) :
  cmon_map (tensor_ump β) (ts_gen g h) ≈ bilin_map β g h.
Proof.
  simpl; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma tensor_ump_tensor_gen {K : AbObject} (β : Bilinear K)
  (g : carrier G) (h : carrier H) :
  cmon_map (tensor_ump β) (bilin_map tensor_gen g h) ≈ bilin_map β g h.
Proof.
  exact (tensor_ump_gen β g h).
Qed.

(* 相关说明。 （已译） *)
Lemma tensor_hom_ext {K : AbObject} (f g : AbHom AbTensor K) :
  (∀ (a : carrier G) (b : carrier H),
      cmon_map f (ts_gen a b) ≈ cmon_map g (ts_gen a b)) →
  ∀ s : tsum, cmon_map f s ≈ cmon_map g s.
Proof.
  intros Hgen s; induction s.
  - exact (Hgen c c0).
  - exact (transitivity (cmon_map_zero f)
             (symmetry (cmon_map_zero g))).
  - refine (transitivity (cmon_map_plus f s1 s2) _).
    refine (transitivity _ (symmetry (cmon_map_plus g s1 s2))).
    exact (cmon_plus_respects K _ _ IHs1 _ _ IHs2).
  - refine (transitivity (ab_map_neg f s) _).
    refine (transitivity _ (symmetry (ab_map_neg g s))).
    exact (ab_neg_respects K _ _ IHs).
Qed.

(* 相关说明。 （已译） *)
Lemma tensor_ump_unique {K : AbObject} (β : Bilinear K)
  (f : AbHom AbTensor K) :
  (∀ (a : carrier G) (b : carrier H),
      cmon_map f (ts_gen a b) ≈ bilin_map β a b) →
  f ≈ tensor_ump β.
Proof.
  intros Hgen s.
  refine (tensor_hom_ext f (tensor_ump β) _ s).
  intros a b.
  exact (transitivity (Hgen a b) (symmetry (tensor_ump_gen β a b))).
Qed.

End Tensor.

Arguments ts_gen {G H} g h.
Arguments ts_zero {G H}.
Arguments ts_plus {G H} s t.
Arguments ts_neg {G H} s.
Arguments ts_eq {G H} s t.
Arguments ts_refl {G H} s.
Arguments te_gen {G H g g' h h'} _ _.
Arguments te_plus {G H s s' t t'} _ _.
Arguments te_neg {G H s s'} _.
Arguments te_assoc {G H} s t u.
Arguments te_comm {G H} s t.
Arguments te_zero_l {G H} s.
Arguments te_neg_l {G H} s.
Arguments te_bilin_l {G H} g g' h.
Arguments te_bilin_r {G H} g h h'.
Arguments te_sym {G H s t} _.
Arguments te_trans {G H s t u} _ _.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance ts_eq_Equivalence_Prop {G H : AbObject} :
  RelationClasses.Equivalence (@ts_eq G H).
Proof.
  constructor.
  - exact ts_refl.
  - exact (fun s t => te_sym).
  - exact (fun s t u => te_trans).
Qed.

#[export] Existing Instance ts_eq_Equivalence.
Arguments AbTensor G H : clear implicits.
Arguments Bilinear G H K : clear implicits.
Arguments bilin_map {G H K} _ _ _.
Arguments bilin_respects {G H K} _.
Arguments bilin_add_l {G H K} _ _ _ _.
Arguments bilin_add_r {G H K} _ _ _ _.
Arguments tensor_gen {G H}.
Arguments tensor_med_fun {G H K} β s.
Arguments tensor_ump {G H K} β.
Arguments tensor_ump_gen {G H K} β g h.
Arguments tensor_hom_ext {G H K} f g _ s.
Arguments tensor_ump_unique {G H K} β f _.

(** ** Bifunctoriality *)

(* The arrow action: map generators extend. Bilinearity the
 复合 generator map point saturation plus bilinearity
 rules target tensor. （已译） *)
Program Definition tensor_map {G G' H H' : AbObject}
  (f : AbHom G G') (k : AbHom H H') :
  AbHom (AbTensor G H) (AbTensor G' H') :=
  tensor_ump (@Build_Bilinear G H (AbTensor G' H')
    (fun g h => ts_gen (cmon_map f g) (cmon_map k h)) _ _ _).
Next Obligation.
  intros G G' H H' f k g g' Hg h h' Hh.
  exact (te_gen (proper_morphism (cmon_map f) _ _ Hg)
                (proper_morphism (cmon_map k) _ _ Hh)).
Qed.
Next Obligation.
  intros G G' H H' f k g g' h.
  refine (te_trans (te_gen (cmon_map_plus f g g') (reflexivity _)) _).
  exact (te_bilin_l _ _ _).
Qed.
Next Obligation.
  intros G G' H H' f k g h h'.
  refine (te_trans (te_gen (reflexivity _) (cmon_map_plus k h h')) _).
  exact (te_bilin_r _ _ _).
Qed.

Lemma tensor_map_gen {G G' H H' : AbObject}
  (f : AbHom G G') (k : AbHom H H') (g : carrier G) (h : carrier H) :
  cmon_map (tensor_map f k) (ts_gen g h)
    ≈ ts_gen (cmon_map f g) (cmon_map k h).
Proof.
  simpl; reflexivity.
Qed.

(* The bifunctor Ab ∏ Ab ⟶ Ab.  Every law is [tensor_hom_ext] plus a
   computation on generators. *)
Program Definition AbTensor_Functor : Ab ∏ Ab ⟶ Ab := {|
  fobj := fun p => AbTensor (fst p) (snd p);
  fmap := fun p q f => tensor_map (fst f) (snd f)
|}.
Next Obligation.
  intros [G H] [G' H'] [f k] [f' k'] [Hf Hk]; simpl in *.
  apply (tensor_hom_ext (tensor_map f k) (tensor_map f' k')).
  intros a b.
  exact (te_gen (Hf a) (Hk b)).
Qed.
Next Obligation.
  intros [G H]; simpl.
  apply (tensor_hom_ext (tensor_map cmon_hom_id cmon_hom_id) cmon_hom_id).
  intros a b; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  intros [G H] [G' H'] [G'' H''] [f k] [f' k']; simpl.
  apply (tensor_hom_ext
           (tensor_map (cmon_hom_compose f f') (cmon_hom_compose k k'))
           (cmon_hom_compose (tensor_map f k) (tensor_map f' k'))).
  intros a b; simpl.
  exact (ts_refl _).
Qed.
