Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.

From Coq Require Import Arith.

Generalizable All Variables.

Local Open Scope nat_scope.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TermEq.

Context (S : Signature).

(** Strict tensor coherence requires equating terms whose types
    involve different parenthesisations of [+] on [nat].  Because
    [nat] addition is associative ONLY up to propositional [=]
    (not definitional), we cannot state e.g. an associator
    [T_assoc : Term S ((m+n)+p) (m+(n+p))] in [Term] alone.  The
    equational theory bridges these via the strict tensor axioms
    [TE_tens_assoc] / [TE_tens_id0_left] / [TE_tens_id0_right]; in
    practice they are used as rewrite rules to bring a term into a
    canonical right-associated form on its arities. *)

Inductive TermEq : forall {m n}, Term S m n -> Term S m n -> Prop :=

  (** Setoid laws. *)
  | TE_refl  : forall {m n} (t : Term S m n), TermEq t t     (* equivalence: reflexivity *)
  | TE_sym   : forall {m n} (s t : Term S m n),              (* equivalence: symmetry *)
               TermEq s t -> TermEq t s
  | TE_trans : forall {m n} (s t u : Term S m n),            (* equivalence: transitivity *)
               TermEq s t -> TermEq t u -> TermEq s u

  (** Congruence of sequential composition. *)
  | TE_comp_cong : forall {m n p}                            (* congruence of [T_comp] *)
                          (f f' : Term S n p) (g g' : Term S m n),
                   TermEq f f' -> TermEq g g' ->
                   TermEq (T_comp f g) (T_comp f' g')

  (** Congruence of parallel composition (tensor). *)
  | TE_tens_cong : forall {m1 n1 m2 n2}                      (* congruence of [T_tens] *)
                          (f f' : Term S m1 n1) (g g' : Term S m2 n2),
                   TermEq f f' -> TermEq g g' ->
                   TermEq (T_tens f g) (T_tens f' g')

  (** Category laws: id-left, id-right, associativity. *)
  | TE_id_left  : forall {m n} (f : Term S m n),             (* category: left identity *)
                  TermEq (T_comp (T_id n) f) f
  | TE_id_right : forall {m n} (f : Term S m n),             (* category: right identity *)
                  TermEq (T_comp f (T_id m)) f
  | TE_assoc    : forall {m n p q}                           (* category: associativity of [⊙] *)
                         (h : Term S p q) (g : Term S n p) (f : Term S m n),
                  TermEq (T_comp (T_comp h g) f)
                         (T_comp h (T_comp g f))

  (** Bifunctor laws: 恒等, sequential interchange.

 [TE_tens_id]: [id_m ⊕ id_n = id_(m+n)] — typing OK because [Term]
 [nat]-indexed addition tensor arities. （已译） *)
  | TE_tens_id : forall (m n : nat),                         (* bifunctor: tensor preserves identity *)
                 TermEq (T_tens (T_id m) (T_id n)) (T_id (m + n))

  (** [TE_interchange]: (f₁ ⊕ g₁) ⊙ (f₂ ⊕ g₂) ≈ (f₁ ⊙ f₂) ⊕ (g₁ ⊙ g₂)
      — the parallel/sequential interchange law. *)
  | TE_interchange :                                         (* bifunctor: middle-four interchange *)
      forall {m1 n1 p1 m2 n2 p2}
             (f1 : Term S n1 p1) (g1 : Term S n2 p2)
             (f2 : Term S m1 n1) (g2 : Term S m2 n2),
        TermEq (T_comp (T_tens f1 g1) (T_tens f2 g2))
               (T_tens (T_comp f1 f2) (T_comp g1 g2))

  (** Braid involution: [σ_{m,n} ⊙ σ_{n,m} ≈ id_{m+n}].  Block-braiding
      twice returns to identity. *)
  | TE_braid_invol :                                         (* symmetry: involution σ⊙σ = id *)
      forall (m n : nat),
        TermEq (T_comp (T_braid n m) (T_braid m n)) (T_id (m + n))

  (** Braid naturality (top form):
        (g ⊕ f) ⊙ σ_{m1,m2} ≈ σ_{n1,n2} ⊙ (f ⊕ g)
      where f : m1 -> n1, g : m2 -> n2. *)
  | TE_braid_natural :                                       (* symmetry: braiding naturality *)
      forall {m1 n1 m2 n2}
             (f : Term S m1 n1) (g : Term S m2 n2),
        TermEq (T_comp (T_tens g f) (T_braid m1 m2))
               (T_comp (T_braid n1 n2) (T_tens f g))

  (*
   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  | TE_tens_id0_left :                                       (* strict unit: left unitor λ = id *)
      forall {m n : nat} (f : Term S m n),
        TermEq (T_tens (T_id 0) f) f

  (*
   本节说明 TermEq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  | TE_tens_id0_right :                                      (* strict unit: right unitor ρ = id *)
      forall {m n : nat} (f : Term S m n),
        TermEq (eq_rect (Nat.add n O)
                        (fun k => Term S (Nat.add m O) k)
                        (T_tens f (T_id O))
                        n
                        (Nat.add_0_r n))
               (eq_rect_r
                  (fun k => Term S k n)
                  f
                  (Nat.add_0_r m))

  (** Strict-PROP associativity of tensor.  Transport form. *)
  | TE_tens_assoc :                                          (* strict associator α = id *)
      forall {m1 n1 m2 n2 m3 n3 : nat}
             (f : Term S m1 n1) (g : Term S m2 n2) (h : Term S m3 n3),
        TermEq (eq_rect (Nat.add (Nat.add n1 n2) n3)
                        (fun k => Term S (Nat.add (Nat.add m1 m2) m3) k)
                        (T_tens (T_tens f g) h)
                        (Nat.add n1 (Nat.add n2 n3))
                        (eq_sym (Nat.add_assoc n1 n2 n3)))
               (eq_rect_r
                  (fun k => Term S k (Nat.add n1 (Nat.add n2 n3)))
                  (T_tens f (T_tens g h))
                  (eq_sym (Nat.add_assoc m1 m2 m3)))

  (*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

  | TE_braid_hex_left :                                       (* symmetry: hexagon (left argument) *)
      forall (m n p : nat),
        TermEq
          (* LHS: σ_{m+n,p} with source cast (m+n)+p → m+(n+p). *)
          (eq_rect ((m + n) + p)
                   (fun s => Term S s (p + (m + n)))
                   (T_braid (m + n) p)
                   (m + (n + p))
                   (eq_sym (Nat.add_assoc m n p)))
          (* RHS: (σ_{m,p} ⊕ id_n) ⊙ (id_m ⊕ σ_{n,p})
             — the outer term needs both source and target casts to
             reach types Term S (m+(p+n)) (p+(m+n)); the inner term
             already has type Term S (m+(n+p)) (m+(p+n)). *)
          (T_comp
             (eq_rect ((p + m) + n)
                      (fun t => Term S (m + (p + n)) t)
                      (eq_rect ((m + p) + n)
                               (fun s => Term S s ((p + m) + n))
                               (T_tens (T_braid m p) (T_id n))
                               (m + (p + n))
                               (eq_sym (Nat.add_assoc m p n)))
                      (p + (m + n))
                      (eq_sym (Nat.add_assoc p m n)))
             (T_tens (T_id m) (T_braid n p)))

  | TE_braid_hex_right :                                      (* symmetry: hexagon (right argument) *)
      forall (m n p : nat),
        TermEq
          (* LHS: σ_{m,n+p} with target cast (n+p)+m → n+(p+m). *)
          (eq_rect ((n + p) + m)
                   (fun t => Term S (m + (n + p)) t)
                   (T_braid m (n + p))
                   (n + (p + m))
                   (eq_sym (Nat.add_assoc n p m)))
          (* RHS: (id_n ⊕ σ_{m,p}) ⊙ (σ_{m,n} ⊕ id_p)
             — outer source: n+(m+p) → (n+m)+p (Nat.add_assoc forward);
               inner source: (m+n)+p → m+(n+p) (eq_sym). *)
          (T_comp
             (eq_rect (n + (m + p))
                      (fun s => Term S s (n + (p + m)))
                      (T_tens (T_id n) (T_braid m p))
                      ((n + m) + p)
                      (Nat.add_assoc n m p))
             (eq_rect ((m + n) + p)
                      (fun s => Term S s ((n + m) + p))
                      (T_tens (T_braid m n) (T_id p))
                      (m + (n + p))
                      (eq_sym (Nat.add_assoc m n p))))

  (*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

  | TE_braid_unit_left :                                      (* symmetry: unit braid σ_{0,n} = id (derivable) *)
      forall (n : nat),
        TermEq
          (* T_braid 0 n : Term S (0+n) (n+0) = Term S n (n+0).
             Cast the target n+0 → n. *)
          (eq_rect (n + 0) (fun t => Term S n t)
                   (T_braid 0 n)
                   n
                   (Nat.add_0_r n))
          (T_id n)

  | TE_braid_unit_right :                                     (* symmetry: unit braid σ_{n,0} = id (derivable) *)
      forall (n : nat),
        TermEq
          (* T_braid n 0 : Term S (n+0) (0+n) = Term S (n+0) n.
             Cast the source n+0 → n. *)
          (eq_rect (n + 0) (fun s => Term S s n)
                   (T_braid n 0)
                   n
                   (Nat.add_0_r n))
          (T_id n).

End TermEq.

Arguments TE_refl  {S m n}.
Arguments TE_sym   {S m n}.
Arguments TE_trans {S m n}.
Arguments TE_comp_cong {S m n p}.
Arguments TE_tens_cong {S m1 n1 m2 n2}.
Arguments TE_id_left  {S m n}.
Arguments TE_id_right {S m n}.
Arguments TE_assoc {S m n p q}.
Arguments TE_tens_id {S}.
Arguments TE_interchange {S m1 n1 p1 m2 n2 p2}.
Arguments TE_braid_invol {S}.
Arguments TE_braid_natural {S m1 n1 m2 n2}.
Arguments TE_tens_id0_left {S m n}.
Arguments TE_tens_id0_right {S m n}.
Arguments TE_tens_assoc {S m1 n1 m2 n2 m3 n3}.
Arguments TE_braid_hex_left {S}.
Arguments TE_braid_hex_right {S}.
Arguments TE_braid_unit_left {S}.
Arguments TE_braid_unit_right {S}.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** An 恒等 slides one side 态射 other. （已译） *)
Lemma tm_id_swap {S : Signature} {m n : nat} (t : Term S m n) :
  TermEq S (T_comp t (T_id m)) (T_comp (T_id n) t).
Proof.
  apply TE_trans with t.
  - apply TE_id_right.
  - apply TE_sym, TE_id_left.
Qed.

(** A composite of identities equals a tensor of identities. *)
Lemma tm_comp_id_tens {S : Signature} (m n : nat) :
  TermEq S (T_comp (T_id (m + n)) (T_id (m + n))) (T_tens (T_id m) (T_id n)).
Proof.
  apply TE_trans with (T_id (m + n)).
  - apply TE_id_left.
  - apply TE_sym, TE_tens_id.
Qed.

(** Collapsing an identity and a tensor of identities after [t]. *)
Lemma tm_collapse_r {S : Signature} {m n p : nat} (t : Term S (m + n) p) :
  TermEq S (T_comp (T_comp t (T_id (m + n))) (T_tens (T_id m) (T_id n))) t.
Proof.
  apply TE_trans with (T_comp t (T_tens (T_id m) (T_id n))).
  - apply TE_comp_cong.
    + apply TE_id_right.
    + apply TE_refl.
  - apply TE_trans with (T_comp t (T_id (m + n))).
    + apply TE_comp_cong.
      * apply TE_refl.
      * apply TE_tens_id.
    + apply TE_id_right.
Qed.

(** Collapsing an identity and a tensor of identities before [t]. *)
Lemma tm_collapse_l {S : Signature} {m n p : nat} (t : Term S p (m + n)) :
  TermEq S (T_comp (T_comp (T_id (m + n)) (T_tens (T_id m) (T_id n))) t) t.
Proof.
  apply TE_trans with (T_comp (T_tens (T_id m) (T_id n)) t).
  - apply TE_comp_cong.
    + apply TE_id_left.
    + apply TE_refl.
  - apply TE_trans with (T_comp (T_id (m + n)) t).
    + apply TE_comp_cong.
      * apply TE_tens_id.
      * apply TE_refl.
    + apply TE_id_left.
Qed.

(*
   本节说明 TermEq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint T_subst {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {m n : nat} (t : Term S m n) : Term T m n :=
  match t in Term _ m' n' return Term T m' n' with
  | T_id k      => T_id k
  | T_braid a b => T_braid a b
  | T_comp g f  => T_comp (T_subst sub g) (T_subst sub f)
  | T_tens f g  => T_tens (T_subst sub f) (T_subst sub g)
  | T_gen s     => sub _ _ s
  end.

(* 相关说明。 （已译） *)

Lemma T_subst_eq_rect_cod {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {a b b' : nat} (e : b = b') (t : Term S a b) :
  T_subst sub (eq_rect b (fun k : nat => Term S a k) t b' e)
  = eq_rect b (fun k : nat => Term T a k) (T_subst sub t) b' e.
Proof. destruct e; reflexivity. Qed.

Lemma T_subst_eq_rect_dom {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {a a' b : nat} (e : a = a') (t : Term S a b) :
  T_subst sub (eq_rect a (fun k : nat => Term S k b) t a' e)
  = eq_rect a (fun k : nat => Term T k b) (T_subst sub t) a' e.
Proof. destruct e; reflexivity. Qed.

Lemma T_subst_eq_rect_r_dom {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {a a' b : nat} (e : a' = a) (t : Term S a b) :
  T_subst sub (eq_rect_r (fun k : nat => Term S k b) t e)
  = eq_rect_r (fun k : nat => Term T k b) (T_subst sub t) e.
Proof. destruct e; reflexivity. Qed.

(*
   本节说明 TermEq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma T_subst_TermEq {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {m n : nat} {s t : Term S m n} :
  TermEq S s t -> TermEq T (T_subst sub s) (T_subst sub t).
Proof.
  intros HT.
  induction HT.
  - (* TE_refl *)
    apply TE_refl.
  - (* TE_sym *)
    exact (TE_sym _ _ IHHT).
  - (* TE_trans *)
    exact (TE_trans _ _ _ IHHT1 IHHT2).
  - (* TE_comp_cong *)
    cbn [T_subst]; apply TE_comp_cong; assumption.
  - (* TE_tens_cong *)
    cbn [T_subst]; apply TE_tens_cong; assumption.
  - (* TE_id_left *)
    cbn [T_subst]; apply TE_id_left.
  - (* TE_id_right *)
    cbn [T_subst]; apply TE_id_right.
  - (* TE_assoc *)
    cbn [T_subst]; apply TE_assoc.
  - (* TE_tens_id *)
    cbn [T_subst]; apply TE_tens_id.
  - (* TE_interchange *)
    cbn [T_subst]; apply TE_interchange.
  - (* TE_braid_invol *)
    cbn [T_subst]; apply TE_braid_invol.
  - (* TE_braid_natural *)
    cbn [T_subst]; apply TE_braid_natural.
  - (* TE_tens_id0_left *)
    cbn [T_subst]; apply TE_tens_id0_left.
  - (* TE_tens_id0_right *)
    rewrite T_subst_eq_rect_cod, T_subst_eq_rect_r_dom.
    cbn [T_subst]; apply TE_tens_id0_right.
  - (* TE_tens_assoc *)
    rewrite T_subst_eq_rect_cod, T_subst_eq_rect_r_dom.
    cbn [T_subst]; apply TE_tens_assoc.
  - (* TE_braid_hex_left *)
    cbn [T_subst].
    rewrite T_subst_eq_rect_cod, !T_subst_eq_rect_dom.
    cbn [T_subst]; apply TE_braid_hex_left.
  - (* TE_braid_hex_right *)
    cbn [T_subst].
    rewrite T_subst_eq_rect_cod, !T_subst_eq_rect_dom.
    cbn [T_subst]; apply TE_braid_hex_right.
  - (* TE_braid_unit_left *)
    rewrite T_subst_eq_rect_cod.
    cbn [T_subst]; apply TE_braid_unit_left.
  - (* TE_braid_unit_right *)
    rewrite T_subst_eq_rect_dom.
    cbn [T_subst]; apply TE_braid_unit_right.
Qed.
