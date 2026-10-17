Require Import Category.Lib.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CFreeMonoidal.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

(* * ** Transport bridges: [eq_rect] spellings vs. [CT_cast] composites

 A codomain transport post-复合 cast; domain
 transport pre-复合 (inverted) cast. Each 证明
 destructs boundary equation, after both sides collapse
 恒等 law [CTermEq]. No decidability involved. （已译） *)

(** Codomain transport equals post-composition with [CT_cast e]. *)
Lemma ceq_rect_cod_cast {a b b' : list Colour}
  (t : CTerm S a b) (e : b = b') :
  CTermEq S (eq_rect b (fun k => CTerm S a k) t b' e)
            (CT_comp (CT_cast e) t).
Proof.
  destruct e; cbn.
  apply CTE_sym, CTE_id_left.
Qed.

(** Domain transport equals pre-composition with [CT_cast (eq_sym e)]. *)
Lemma ceq_rect_dom_cast {a a' b : list Colour}
  (t : CTerm S a b) (e : a = a') :
  CTermEq S (eq_rect a (fun k => CTerm S k b) t a' e)
            (CT_comp t (CT_cast (eq_sym e))).
Proof.
  destruct e; cbn.
  apply CTE_sym, CTE_id_right.
Qed.

(** Reverse-direction domain transport ([eq_rect_r]) equals
    pre-composition with [CT_cast e] directly. *)
Lemma ceq_rect_r_dom_cast {a a' b : list Colour}
  (t : CTerm S a b) (e : a' = a) :
  CTermEq S (eq_rect_r (fun k => CTerm S k b) t e)
            (CT_comp t (CT_cast e)).
Proof.
  destruct e; cbn.
  apply CTE_sym, CTE_id_right.
Qed.

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma CT_cast_sym_sym {cs ds : list Colour} (e : cs = ds) :
  CT_cast (S := S) (eq_sym (eq_sym e)) = CT_cast e.
Proof. destruct e; reflexivity. Qed.

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma ccast_shift_l {a b c : list Colour} (e : a = b)
  (f : CTerm S b c) (g : CTerm S a c) :
  CTermEq S (CT_comp f (CT_cast e)) g ->
  CTermEq S f (CT_comp g (CT_cast (eq_sym e))).
Proof.
  destruct e; cbn; intros H.
  apply CTE_trans with g.
  - apply CTE_trans with (CT_comp f (CT_id a)).
    + apply CTE_sym, CTE_id_right.
    + exact H.
  - apply CTE_sym, CTE_id_right.
Qed.

Lemma ccast_shift_r {a b c : list Colour} (e : b = c)
  (f : CTerm S a b) (g : CTerm S a c) :
  CTermEq S (CT_comp (CT_cast e) f) g ->
  CTermEq S f (CT_comp (CT_cast (eq_sym e)) g).
Proof.
  destruct e; cbn; intros H.
  apply CTE_trans with g.
  - apply CTE_trans with (CT_comp (CT_id b) f).
    + apply CTE_sym, CTE_id_left.
    + exact H.
  - apply CTE_sym, CTE_id_left.
Qed.

(** Flipping a naturality square along both casts: from
    [q ∘ cast ≈ cast ∘ p] conclude [p ∘ cast⁻¹ ≈ cast⁻¹ ∘ q].
    This turns every [to]-direction structural naturality square
    into its [from]-direction companion. *)
Lemma ccast_square_flip {a b c d : list Colour} (e1 : a = b) (e2 : c = d)
  (p : CTerm S a c) (q : CTerm S b d) :
  CTermEq S (CT_comp q (CT_cast e1)) (CT_comp (CT_cast e2) p) ->
  CTermEq S (CT_comp p (CT_cast (eq_sym e1))) (CT_comp (CT_cast (eq_sym e2)) q).
Proof.
  destruct e1, e2; cbn; intros H.
  assert (Hqp : CTermEq S q p).
  { apply CTE_trans with (CT_comp q (CT_id a)).
    - apply CTE_sym, CTE_id_right.
    - apply CTE_trans with (CT_comp (CT_id c) p).
      + exact H.
      + apply CTE_id_left. }
  apply CTE_trans with p.
  - apply CTE_id_right.
  - apply CTE_trans with q.
    + apply CTE_sym, Hqp.
    + apply CTE_sym, CTE_id_left.
Qed.

(* * ** Tensor fusion

 A tensor 态射 decomposes either sliding order the
 two "half-恒等" tensors; both composites fuse back the
 plain tensor via interchange law. （已译） *)

Lemma ctens_fuse_l {a b c d : list Colour}
  (f : CTerm S a b) (g : CTerm S c d) :
  CTermEq S (CT_comp (CT_tens f (CT_id d)) (CT_tens (CT_id a) g))
            (CT_tens f g).
Proof.
  apply CTE_trans with (CT_tens (CT_comp f (CT_id a)) (CT_comp (CT_id d) g)).
  - apply CTE_interchange.
  - apply CTE_tens_cong.
    + apply CTE_id_right.
    + apply CTE_id_left.
Qed.

Lemma ctens_fuse_r {a b c d : list Colour}
  (f : CTerm S a b) (g : CTerm S c d) :
  CTermEq S (CT_comp (CT_tens (CT_id b) g) (CT_tens f (CT_id c)))
            (CT_tens f g).
Proof.
  apply CTE_trans with (CT_tens (CT_comp (CT_id b) f) (CT_comp g (CT_id c))).
  - apply CTE_interchange.
  - apply CTE_tens_cong.
    + apply CTE_id_left.
    + apply CTE_id_right.
Qed.

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cleft_unit_natural {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp g (CT_cast (app_nil_l x)))
            (CT_comp (CT_cast (app_nil_l y)) (CT_tens (CT_id []) g)).
Proof using Cdec.
  rewrite (CT_cast_id Cdec (app_nil_l x)).
  rewrite (CT_cast_id Cdec (app_nil_l y)).
  apply CTE_trans with g.
  - apply CTE_id_right.
  - apply CTE_sym.
    apply CTE_trans with (CT_tens (CT_id []) g).
    + apply CTE_id_left.
    + apply CTE_tens_id0_left.
Qed.

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cleft_unit_natural_from {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp (CT_tens (CT_id []) g) (CT_cast (eq_sym (app_nil_l x))))
            (CT_comp (CT_cast (eq_sym (app_nil_l y))) g).
Proof using Cdec.
  apply ccast_square_flip, cleft_unit_natural.
Qed.

(* 相关说明。 （已译） *)

(** Tensoring 恒等 [CT_id []] left collapses a
 single 恒等 term. （已译） *)
Lemma ctens_id0_id (n : list Colour) :
  CTermEq S (CT_tens (CT_id []) (CT_id n)) (CT_id n).
Proof. apply CTE_tens_id0_left. Qed.

(** Repeated tensor of [CT_id []] on the left is still [CT_id []]. *)
Lemma ctens_id0_id0 :
  CTermEq S (CT_tens (CT_id []) (CT_id [])) (CT_id []).
Proof. apply CTE_tens_id0_left. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma ctens_id0_right_at_0 (f : CTerm S [] []) :
  CTermEq S (CT_tens f (CT_id [])) f.
Proof using Cdec.
  pose proof (CTE_tens_id0_right f) as Hr.
  unfold eq_rect_r in Hr.
  rewrite (UIP_dec (list_eq_dec Cdec)
             (app_nil_r (@nil Colour)) eq_refl) in Hr.
  cbn in Hr.
  exact Hr.
Qed.

(* 相关说明。 （已译） *)

Lemma ctens_id0_right_at {m n : list Colour} (f : CTerm S m n) :
  CTermEq S
    (eq_rect (n ++ []) (fun k => CTerm S (m ++ []) k)
             (CT_tens f (CT_id [])) n (app_nil_r n))
    (eq_rect_r (fun k => CTerm S k n) f (app_nil_r m)).
Proof. exact (CTE_tens_id0_right f). Qed.

(* 相关说明。 （已译） *)

Lemma ctens_assoc_at {m1 n1 m2 n2 m3 n3 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) (h : CTerm S m3 n3) :
  CTermEq S
    (eq_rect ((n1 ++ n2) ++ n3)
             (fun k => CTerm S ((m1 ++ m2) ++ m3) k)
             (CT_tens (CT_tens f g) h)
             (n1 ++ (n2 ++ n3))
             (eq_sym (app_assoc n1 n2 n3)))
    (eq_rect_r (fun k => CTerm S k (n1 ++ (n2 ++ n3)))
               (CT_tens f (CT_tens g h))
               (eq_sym (app_assoc m1 m2 m3))).
Proof. exact (CTE_tens_assoc f g h). Qed.

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cright_unit_natural {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp g (CT_cast (app_nil_r x)))
            (CT_comp (CT_cast (app_nil_r y)) (CT_tens g (CT_id []))).
Proof.
  apply CTE_sym.
  apply CTE_trans with
    (eq_rect (y ++ []) (fun k => CTerm S (x ++ []) k)
             (CT_tens g (CT_id [])) y (app_nil_r y)).
  - apply CTE_sym, ceq_rect_cod_cast.
  - apply CTE_trans with (eq_rect_r (fun k => CTerm S k y) g (app_nil_r x)).
    + apply CTE_tens_id0_right.
    + apply ceq_rect_r_dom_cast.
Qed.

(** 本节：The [from]-direction square [(g ⊕c id_[]) ∘ ρ⁻¹ ≈ ρ⁻¹ ∘ g]. （已译） *)
Lemma cfrom_right_unit_natural {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp (CT_tens g (CT_id [])) (CT_cast (eq_sym (app_nil_r x))))
            (CT_comp (CT_cast (eq_sym (app_nil_r y))) g).
Proof.
  apply ccast_square_flip, cright_unit_natural.
Qed.

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cassoc_natural {m1 n1 m2 n2 m3 n3 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) (h : CTerm S m3 n3) :
  CTermEq S
    (CT_comp (CT_tens f (CT_tens g h))
             (CT_cast (eq_sym (app_assoc m1 m2 m3))))
    (CT_comp (CT_cast (eq_sym (app_assoc n1 n2 n3)))
             (CT_tens (CT_tens f g) h)).
Proof.
  apply CTE_trans with
    (eq_rect_r (fun k => CTerm S k (n1 ++ (n2 ++ n3)))
               (CT_tens f (CT_tens g h))
               (eq_sym (app_assoc m1 m2 m3))).
  - apply CTE_sym, ceq_rect_r_dom_cast.
  - apply CTE_trans with
      (eq_rect ((n1 ++ n2) ++ n3)
               (fun k => CTerm S ((m1 ++ m2) ++ m3) k)
               (CT_tens (CT_tens f g) h)
               (n1 ++ (n2 ++ n3))
               (eq_sym (app_assoc n1 n2 n3))).
    + apply CTE_sym, CTE_tens_assoc.
    + apply ceq_rect_cod_cast.
Qed.

(** 本节：The [from]-direction square
 [((f ⊕c g) ⊕c h) ∘ α⁻¹ ≈ α⁻¹ ∘ (f ⊕c (g ⊕c h))]. （已译） *)
Lemma cfrom_assoc_natural {m1 n1 m2 n2 m3 n3 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) (h : CTerm S m3 n3) :
  CTermEq S
    (CT_comp (CT_tens (CT_tens f g) h) (CT_cast (app_assoc m1 m2 m3)))
    (CT_comp (CT_cast (app_assoc n1 n2 n3)) (CT_tens f (CT_tens g h))).
Proof.
  rewrite <- (CT_cast_sym_sym (app_assoc m1 m2 m3)).
  rewrite <- (CT_cast_sym_sym (app_assoc n1 n2 n3)).
  apply ccast_square_flip, cassoc_natural.
Qed.

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cfree_triangle (x y : list Colour) :
  CTermEq S (CT_tens (CT_cast (app_nil_r x)) (CT_id y))
            (CT_comp (CT_tens (CT_id x) (CT_cast (app_nil_l y)))
                     (CT_cast (eq_sym (app_assoc x [] y)))).
Proof using Cdec.
  apply CTE_trans with
    (CT_cast (f_equal (fun ks => ks ++ y) (app_nil_r x))).
  - apply CT_tens_cast_id_right.
  - apply CTE_sym.
    apply CTE_trans with
      (CT_comp (CT_cast (f_equal (fun ks => x ++ ks) (app_nil_l y)))
               (CT_cast (eq_sym (app_assoc x [] y)))).
    + apply CTE_comp_cong.
      * apply CT_tens_id_cast_left.
      * apply CTE_refl.
    + apply CTE_trans with
        (CT_cast (eq_trans (eq_sym (app_assoc x [] y))
                           (f_equal (fun ks => x ++ ks) (app_nil_l y)))).
      * apply CT_cast_compose.
      * rewrite (CT_cast_irrelevant Cdec
                   (eq_trans (eq_sym (app_assoc x [] y))
                             (f_equal (fun ks => x ++ ks) (app_nil_l y)))
                   (f_equal (fun ks => ks ++ y) (app_nil_r x))).
        apply CTE_refl.
Qed.

(*
   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cfree_pentagon (x y z w : list Colour) :
  CTermEq S
    (CT_comp (CT_comp (CT_tens (CT_id x)
                               (CT_cast (eq_sym (app_assoc y z w))))
                      (CT_cast (eq_sym (app_assoc x (y ++ z) w))))
             (CT_tens (CT_cast (eq_sym (app_assoc x y z))) (CT_id w)))
    (CT_comp (CT_cast (eq_sym (app_assoc x y (z ++ w))))
             (CT_cast (eq_sym (app_assoc (x ++ y) z w)))).
Proof using Cdec.
  apply CTE_trans with
    (CT_comp (CT_comp (CT_cast (f_equal (fun ks => x ++ ks)
                                        (eq_sym (app_assoc y z w))))
                      (CT_cast (eq_sym (app_assoc x (y ++ z) w))))
             (CT_cast (f_equal (fun ks => ks ++ w)
                               (eq_sym (app_assoc x y z))))).
  - apply CTE_comp_cong.
    + apply CTE_comp_cong.
      * apply CT_tens_id_cast_left.
      * apply CTE_refl.
    + apply CT_tens_cast_id_right.
  - apply CTE_trans with
      (CT_comp (CT_cast (eq_trans (eq_sym (app_assoc x (y ++ z) w))
                                  (f_equal (fun ks => x ++ ks)
                                           (eq_sym (app_assoc y z w)))))
               (CT_cast (f_equal (fun ks => ks ++ w)
                                 (eq_sym (app_assoc x y z))))).
    + apply CTE_comp_cong.
      * apply CT_cast_compose.
      * apply CTE_refl.
    + apply CTE_trans with
        (CT_cast (eq_trans (f_equal (fun ks => ks ++ w)
                                    (eq_sym (app_assoc x y z)))
                           (eq_trans (eq_sym (app_assoc x (y ++ z) w))
                                     (f_equal (fun ks => x ++ ks)
                                              (eq_sym (app_assoc y z w)))))).
      * apply CT_cast_compose.
      * apply CTE_sym.
        apply CTE_trans with
          (CT_cast (eq_trans (eq_sym (app_assoc (x ++ y) z w))
                             (eq_sym (app_assoc x y (z ++ w))))).
        -- apply CT_cast_compose.
        -- rewrite (CT_cast_irrelevant Cdec
                      (eq_trans (eq_sym (app_assoc (x ++ y) z w))
                                (eq_sym (app_assoc x y (z ++ w))))
                      (eq_trans (f_equal (fun ks => ks ++ w)
                                         (eq_sym (app_assoc x y z)))
                                (eq_trans (eq_sym (app_assoc x (y ++ z) w))
                                          (f_equal (fun ks => x ++ ks)
                                                   (eq_sym (app_assoc y z w)))))).
           apply CTE_refl.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition CFreeCat_Monoidal : @Monoidal (CFreeCat S) := {|
  I            := ([] : list Colour);
  tensor       := CFreeCat_Tensor S;
  unit_left    := fun x => CFreeCat_unit_left S x;
  unit_right   := fun x => CFreeCat_unit_right S x;
  tensor_assoc := fun x y z => CFreeCat_tensor_assoc S x y z;
  to_unit_left_natural      := fun x y g => cleft_unit_natural g;
  from_unit_left_natural    := fun x y g => cleft_unit_natural_from g;
  to_unit_right_natural     := fun x y g => cright_unit_natural g;
  from_unit_right_natural   := fun x y g => cfrom_right_unit_natural g;
  to_tensor_assoc_natural   := fun _ _ _ _ _ _ g h i => cassoc_natural g h i;
  from_tensor_assoc_natural := fun _ _ _ _ _ _ g h i =>
                                 cfrom_assoc_natural g h i;
  triangle_identity := fun x y => cfree_triangle x y;
  pentagon_identity := fun x y z w => cfree_pentagon x y z w
|}.

End CFreeMonoidal.

Arguments CFreeCat_Monoidal {Colour} S Cdec : assert.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
