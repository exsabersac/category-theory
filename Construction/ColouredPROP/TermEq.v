Require Import Category.Lib.
Require Import Category.Construction.ColouredPROP.Signature.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Equational theory of free coloured-PROP terms *)

(*
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CTermEq.

Context {Colour : Type}.
Context (S : CSignature Colour).

(** Strict tensor coherence requires equating terms whose types
    involve different parenthesisations of [++] on [list Colour].
    Because concatenation is associative ONLY up to propositional [=]
    (not definitional), we cannot state e.g. an associator
    [CT_assoc : CTerm S ((cs ++ ds) ++ es) (cs ++ (ds ++ es))] in
    [CTerm] alone.  The equational theory bridges these via the strict
    tensor axioms [CTE_tens_assoc] / [CTE_tens_id0_left] /
    [CTE_tens_id0_right]; in practice they are used as rewrite rules to
    bring a term into a canonical right-associated form on its
    boundaries. *)

Inductive CTermEq : forall {cs ds}, CTerm S cs ds -> CTerm S cs ds -> Prop :=

  (** Setoid laws. *)
  | CTE_refl {cs ds} (f : CTerm S cs ds) :                   (* equivalence: reflexivity *)
      CTermEq f f
  | CTE_sym {cs ds} (f g : CTerm S cs ds) :                  (* equivalence: symmetry *)
      CTermEq f g -> CTermEq g f
  | CTE_trans {cs ds} (f g h : CTerm S cs ds) :              (* equivalence: transitivity *)
      CTermEq f g -> CTermEq g h -> CTermEq f h

  (** Congruence of sequential composition. *)
  | CTE_comp_cong {cs ds es}                                 (* congruence of [CT_comp] *)
      (f f' : CTerm S ds es) (g g' : CTerm S cs ds) :
      CTermEq f f' -> CTermEq g g' ->
      CTermEq (CT_comp f g) (CT_comp f' g')

  (** Congruence of parallel composition (tensor). *)
  | CTE_tens_cong {cs1 ds1 cs2 ds2}                          (* congruence of [CT_tens] *)
      (f f' : CTerm S cs1 ds1) (g g' : CTerm S cs2 ds2) :
      CTermEq f f' -> CTermEq g g' ->
      CTermEq (CT_tens f g) (CT_tens f' g')

  (** Category laws: id-left, id-right, associativity. *)
  | CTE_id_left {cs ds} (f : CTerm S cs ds) :                (* category: left identity *)
      CTermEq (CT_comp (CT_id ds) f) f
  | CTE_id_right {cs ds} (f : CTerm S cs ds) :               (* category: right identity *)
      CTermEq (CT_comp f (CT_id cs)) f
  | CTE_assoc {cs ds es fs}                                  (* category: associativity of [⊙c] *)
      (h : CTerm S es fs) (g : CTerm S ds es) (f : CTerm S cs ds) :
      CTermEq (CT_comp (CT_comp h g) f)
              (CT_comp h (CT_comp g f))

  (** Bifunctor laws: identity, sequential interchange.

      [CTE_tens_id]: [id_cs ⊕c id_ds = id_(cs ++ ds)] — typing OK
      because [CTerm] is [list Colour]-indexed and concatenation is
      the tensor on boundaries. *)
  | CTE_tens_id (cs ds : list Colour) :                      (* bifunctor: tensor preserves identity *)
      CTermEq (CT_tens (CT_id cs) (CT_id ds)) (CT_id (cs ++ ds))

  (** [CTE_interchange]: (f₁ ⊕c g₁) ⊙c (f₂ ⊕c g₂) ≈ (f₁ ⊙c f₂) ⊕c (g₁ ⊙c g₂)
      — the parallel/sequential interchange law. *)
  | CTE_interchange {cs ds es cs' ds' es'}                   (* bifunctor: middle-four interchange *)
      (f1 : CTerm S ds es) (f2 : CTerm S cs ds)
      (g1 : CTerm S ds' es') (g2 : CTerm S cs' ds') :
      CTermEq (CT_comp (CT_tens f1 g1) (CT_tens f2 g2))
              (CT_tens (CT_comp f1 f2) (CT_comp g1 g2))

  (** Braid involution: [σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id_{cs ++ ds}].
      Block-braiding twice returns to identity. *)
  | CTE_braid_invol (cs ds : list Colour) :                  (* symmetry: involution σ⊙σ = id *)
      CTermEq (CT_comp (CT_braid ds cs) (CT_braid cs ds)) (CT_id (cs ++ ds))

  (** Braid naturality (top form):
        (g ⊕c f) ⊙c σ_{cs1,cs2} ≈ σ_{ds1,ds2} ⊙c (f ⊕c g)
      where f : cs1 -> ds1, g : cs2 -> ds2. *)
  | CTE_braid_natural {cs1 ds1 cs2 ds2}                      (* symmetry: braiding naturality *)
      (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) :
      CTermEq (CT_comp (CT_tens g f) (CT_braid cs1 cs2))
              (CT_comp (CT_braid ds1 ds2) (CT_tens f g))

  (*
   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  | CTE_tens_id0_left {cs ds} (f : CTerm S cs ds) :          (* strict unit: left unitor λ = id *)
      CTermEq (CT_tens (CT_id []) f) f

  (*
   本节说明 TermEq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  | CTE_tens_id0_right {cs ds} (f : CTerm S cs ds) :         (* strict unit: right unitor ρ = id *)
      CTermEq (eq_rect (ds ++ [])
                       (fun k => CTerm S (cs ++ []) k)
                       (CT_tens f (CT_id []))
                       ds
                       (app_nil_r ds))
              (eq_rect_r (fun k => CTerm S k ds)
                         f
                         (app_nil_r cs))

  (** Strict-PROP associativity of tensor.  Transport form. *)
  | CTE_tens_assoc {cs1 ds1 cs2 ds2 cs3 ds3}                 (* strict associator α = id *)
      (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) (h : CTerm S cs3 ds3) :
      CTermEq (eq_rect ((ds1 ++ ds2) ++ ds3)
                       (fun k => CTerm S ((cs1 ++ cs2) ++ cs3) k)
                       (CT_tens (CT_tens f g) h)
                       (ds1 ++ (ds2 ++ ds3))
                       (eq_sym (app_assoc ds1 ds2 ds3)))
              (eq_rect_r (fun k => CTerm S k (ds1 ++ (ds2 ++ ds3)))
                         (CT_tens f (CT_tens g h))
                         (eq_sym (app_assoc cs1 cs2 cs3)))

  (*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

  | CTE_braid_hex_left (m n p : list Colour) :               (* symmetry: hexagon (left argument) *)
      CTermEq
        (* LHS: σ_{m++n,p} with source cast (m++n)++p → m++(n++p). *)
        (eq_rect ((m ++ n) ++ p)
                 (fun s => CTerm S s (p ++ (m ++ n)))
                 (CT_braid (m ++ n) p)
                 (m ++ (n ++ p))
                 (eq_sym (app_assoc m n p)))
        (* RHS: (σ_{m,p} ⊕c id_n) ⊙c (id_m ⊕c σ_{n,p})
           — the outer term needs both source and target casts to
           reach type CTerm S (m++(p++n)) (p++(m++n)); the inner term
           already has type CTerm S (m++(n++p)) (m++(p++n)). *)
        (CT_comp
           (eq_rect ((p ++ m) ++ n)
                    (fun t => CTerm S (m ++ (p ++ n)) t)
                    (eq_rect ((m ++ p) ++ n)
                             (fun s => CTerm S s ((p ++ m) ++ n))
                             (CT_tens (CT_braid m p) (CT_id n))
                             (m ++ (p ++ n))
                             (eq_sym (app_assoc m p n)))
                    (p ++ (m ++ n))
                    (eq_sym (app_assoc p m n)))
           (CT_tens (CT_id m) (CT_braid n p)))

  | CTE_braid_hex_right (m n p : list Colour) :              (* symmetry: hexagon (right argument) *)
      CTermEq
        (* LHS: σ_{m,n++p} with target cast (n++p)++m → n++(p++m). *)
        (eq_rect ((n ++ p) ++ m)
                 (fun t => CTerm S (m ++ (n ++ p)) t)
                 (CT_braid m (n ++ p))
                 (n ++ (p ++ m))
                 (eq_sym (app_assoc n p m)))
        (* RHS: (id_n ⊕c σ_{m,p}) ⊙c (σ_{m,n} ⊕c id_p)
           — outer source: n++(m++p) → (n++m)++p (app_assoc forward);
             inner source: (m++n)++p → m++(n++p) (eq_sym). *)
        (CT_comp
           (eq_rect (n ++ (m ++ p))
                    (fun s => CTerm S s (n ++ (p ++ m)))
                    (CT_tens (CT_id n) (CT_braid m p))
                    ((n ++ m) ++ p)
                    (app_assoc n m p))
           (eq_rect ((m ++ n) ++ p)
                    (fun s => CTerm S s ((n ++ m) ++ p))
                    (CT_tens (CT_braid m n) (CT_id p))
                    (m ++ (n ++ p))
                    (eq_sym (app_assoc m n p))))

  (*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

  | CTE_braid_unit_left (n : list Colour) :                  (* symmetry: unit braid σ_{[],n} = id (derivable) *)
      CTermEq
        (* CT_braid [] n : CTerm S ([] ++ n) (n ++ []) = CTerm S n (n ++ []).
           Cast the target n ++ [] → n. *)
        (eq_rect (n ++ []) (fun t => CTerm S n t)
                 (CT_braid [] n)
                 n
                 (app_nil_r n))
        (CT_id n)

  | CTE_braid_unit_right (n : list Colour) :                 (* symmetry: unit braid σ_{n,[]} = id (derivable) *)
      CTermEq
        (* CT_braid n [] : CTerm S (n ++ []) ([] ++ n) = CTerm S (n ++ []) n.
           Cast the source n ++ [] → n. *)
        (eq_rect (n ++ []) (fun s => CTerm S s n)
                 (CT_braid n [])
                 n
                 (app_nil_r n))
        (CT_id n).

End CTermEq.

Arguments CTE_refl  {Colour S cs ds}.
Arguments CTE_sym   {Colour S cs ds}.
Arguments CTE_trans {Colour S cs ds}.
Arguments CTE_comp_cong {Colour S cs ds es}.
Arguments CTE_tens_cong {Colour S cs1 ds1 cs2 ds2}.
Arguments CTE_id_left  {Colour S cs ds}.
Arguments CTE_id_right {Colour S cs ds}.
Arguments CTE_assoc {Colour S cs ds es fs}.
Arguments CTE_tens_id {Colour S}.
Arguments CTE_interchange {Colour S cs ds es cs' ds' es'}.
Arguments CTE_braid_invol {Colour S}.
Arguments CTE_braid_natural {Colour S cs1 ds1 cs2 ds2}.
Arguments CTE_tens_id0_left {Colour S cs ds}.
Arguments CTE_tens_id0_right {Colour S cs ds}.
Arguments CTE_tens_assoc {Colour S cs1 ds1 cs2 ds2 cs3 ds3}.
Arguments CTE_braid_hex_left {Colour S}.
Arguments CTE_braid_hex_right {Colour S}.
Arguments CTE_braid_unit_left {Colour S}.
Arguments CTE_braid_unit_right {Colour S}.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** An identity slides from one side of a morphism to the other. *)
Lemma ctm_id_swap {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (t : CTerm S cs ds) :
  CTermEq S (CT_comp t (CT_id cs)) (CT_comp (CT_id ds) t).
Proof.
  apply CTE_trans with t.
  - apply CTE_id_right.
  - apply CTE_sym, CTE_id_left.
Qed.

(** A composite of identities equals a tensor of identities. *)
Lemma ctm_comp_id_tens {Colour : Type} {S : CSignature Colour}
  (m n : list Colour) :
  CTermEq S (CT_comp (CT_id (m ++ n)) (CT_id (m ++ n)))
            (CT_tens (CT_id m) (CT_id n)).
Proof.
  apply CTE_trans with (CT_id (m ++ n)).
  - apply CTE_id_left.
  - apply CTE_sym, CTE_tens_id.
Qed.

(** Collapsing an identity and a tensor of identities after [t]. *)
Lemma ctm_collapse_r {Colour : Type} {S : CSignature Colour}
  {m n p : list Colour} (t : CTerm S (m ++ n) p) :
  CTermEq S (CT_comp (CT_comp t (CT_id (m ++ n)))
                     (CT_tens (CT_id m) (CT_id n))) t.
Proof.
  apply CTE_trans with (CT_comp t (CT_tens (CT_id m) (CT_id n))).
  - apply CTE_comp_cong.
    + apply CTE_id_right.
    + apply CTE_refl.
  - apply CTE_trans with (CT_comp t (CT_id (m ++ n))).
    + apply CTE_comp_cong.
      * apply CTE_refl.
      * apply CTE_tens_id.
    + apply CTE_id_right.
Qed.

(** Collapsing an identity and a tensor of identities before [t]. *)
Lemma ctm_collapse_l {Colour : Type} {S : CSignature Colour}
  {m n p : list Colour} (t : CTerm S p (m ++ n)) :
  CTermEq S (CT_comp (CT_comp (CT_id (m ++ n))
                              (CT_tens (CT_id m) (CT_id n))) t) t.
Proof.
  apply CTE_trans with (CT_comp (CT_tens (CT_id m) (CT_id n)) t).
  - apply CTE_comp_cong.
    + apply CTE_id_left.
    + apply CTE_refl.
  - apply CTE_trans with (CT_comp (CT_id (m ++ n)) t).
    + apply CTE_comp_cong.
      * apply CTE_tens_id.
      * apply CTE_refl.
    + apply CTE_id_left.
Qed.
