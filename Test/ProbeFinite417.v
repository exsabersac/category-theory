Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Span.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Two.
Require Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Fun.Closed.

Generalizable All Variables.

Open Scope category_scope.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeFinite417。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check probe417_nonexistent_name.

(* * ** A: cone-范畴 reading (Instance/Cones/Limit.v) （已译） *)

Section Cones.
  Context `(F : J ⟶ C).

  (* Control: the covariant spelling IS terminality in [Cocones F]. *)
  Example p417_initial_op_is_terminal :
    @Initial (Opposite (Cocones F)) = @Terminal (Cocones F) := eq_refl.

  (* N1 CONVERSION: the issue's literal [Initial (Cocones F)] is a DIFFERENT
     type (terminality in [(Cocones F)^op]). *)
  Fail Example p417_initial_is_not_terminal :
    @Initial (Cocones F) = @Terminal (Cocones F) := eq_refl.

  (* N2 TYPING: literal passage issue asks for,
 [Initial (Cocones F) → Colimit F], refused — 假设 has the
 WRONG type [Colimit_Cocones], plain has-type mismatch. （已译） *)
  Fail Definition p417_colimit_of_initial (I : @Initial (Cocones F)) :
    Colimit F := Colimit_Cocones F I.

  Context (L : Limit F).

  (* 相关说明。 （已译） *)
  Example p417_round_cone :
    @limit_cone _ _ _ (@Limit_Cones _ _ F (Cones_Limit F L))
    = @limit_cone _ _ _ L := eq_refl.
  Example p417_round_med (N : Cone F) :
    unique_obj (@ump_limits _ _ _ (@Limit_Cones _ _ F (Cones_Limit F L)) N)
    = unique_obj (@ump_limits _ _ _ L N) := eq_refl.

  (* N3 CONVERSION: the whole [Limit] record is rebuilt. *)
  Fail Example p417_round_limit_record :
    @Limit_Cones _ _ F (Cones_Limit F L) = L := eq_refl.

  Context (T : @Terminal (Cones F)).

  (* Controls: other round trip returns terminal cone the
 apex map 唯一箭头 nose. （已译） *)
  Example p417_round_terminal_obj :
    @terminal_obj _ (Cones_Limit F (@Limit_Cones _ _ F T)) = @terminal_obj _ T
    := eq_refl.
  Example p417_round_one (N : Cone F) :
    `1 (@one _ (Cones_Limit F (@Limit_Cones _ _ F T)) N) = `1 (@one _ T N)
    := eq_refl.

  (* N4 CONVERSION: the whole [Terminal] record is rebuilt. *)
  Fail Example p417_round_terminal_record :
    Cones_Limit F (@Limit_Cones _ _ F T) = T := eq_refl.
End Cones.

(* 相关说明。 （已译） *)

Section NotComplete.
  Context {C : Category} (FC : @FinitelyComplete C).

  (* N5 CONVERSION: a finitely complete category is not thereby complete —
     a has-type mismatch whose [cannot unify] clause compares the SECOND
     binders ([J ⟶ C] against [FiniteCategory J]), classified by the
     clause as the header table has it. *)
  Fail Definition p417_fc_is_complete : @Complete C := FC.

  (* 相关说明。 （已译） *)
  Definition p417_complete_fc (HC : @Complete C) : @FinitelyComplete C :=
    Complete_FinitelyComplete HC.

  (* N6 TYPING: generator 推论 fed coequalizers where it asks for
 equalizers. （已译） *)
  Fail Definition p417_wrong_generator (T : @Terminal C) (CP : @Cartesian C)
    (HCo : HasCoequalizers C) : @FinitelyComplete C :=
    finitely_complete_from_generators T CP HCo.
End NotComplete.

(** ** C: universes *)

(* A bare clone [EmptyDiagram]: target's explicit binders what
 keep ambient 范畴 free literal [Set]. （已译） *)
Definition EmptyDiagram_bare (C : Category) : EmptyShape ⟶ C.
Proof.
  unshelve refine (@Build_Functor EmptyShape C
    (fun x => False_rect _ x) (fun x y _ => False_rect _ x) _ _ _);
    intros; contradiction.
Defined.

Section UnivPin.
  Universes co ch.
  Constraint Set < ch.
  Context (Cu : Category@{co ch ch}).
  Context (FC : @FinitelyComplete Cu).

  (* 相关说明。 （已译） *)
  Check (@FinitelyComplete Cu).
  Check (FinitelyComplete_Terminal FC).
  Check (FinitelyComplete_HasPullbacks FC).
  Check (FinitelyComplete_Cartesian FC).
  Check (FinitelyComplete_HasEqualizers FC).
  Check (FinitelyComplete_iff_pullbacks_terminal Cu).
  Check (EmptyDiagram Cu).
  Check (@empty_cone Cu).
  Context (DR : Opposite Roof ⟶ Cu).
  Check (FC (Opposite Roof) Cospan_FiniteCategory DR).
  Context (DP : Parallel ⟶ Cu).
  Check (FC Parallel Parallel_FiniteCategory DP).

  (* 相关说明。 （已译） *)
  Fail Check (EmptyDiagram_bare Cu).

  (* 相关说明。 （已译） *)
  Context (D2 : _2 ⟶ Cu).
  Check D2.
  Fail Check (Limit D2).
  Fail Check (FC _2 Two_FiniteCategory D2).
End UnivPin.

Section HomProof.
  Universes jo jh jp.
  Constraint jh < jp.
  Context (Jv : Category@{jo jh jp}).
  Context (x y : Jv) (f : x ~> y).
  Check f.
  Check (id[x]).
  (* N9 UNIVERSE: [FiniteCategory] identifies shape's hom 证明
 universes (through [ArrowIx]; measured). （已译） *)
  Fail Check (@ArrowIx Jv).
  Fail Check (FiniteCategory Jv).
End HomProof.

(** ** D: witnesses *)

Definition FinSet_FinitelyComplete_pb : @FinitelyComplete FinSet :=
  finitely_complete_of_pullbacks_terminal FinSet_Pullbacks FinSet_Terminal.

Definition FinSet_FinitelyCocomplete : @FinitelyCocomplete FinSet :=
  finitely_cocomplete_of_pushouts_initial FinSet_HasPushouts FinSet_Initial.

Definition Sets_FinitelyComplete : @FinitelyComplete Sets :=
  finitely_complete_of_pullbacks_terminal Sets_HasPullbacks Sets_Terminal.

(* 相关说明。 （已译） *)
Definition topos_FinitelyComplete {C : Category} (T : ElementaryTopos C) :
  @FinitelyComplete C :=
  finitely_complete_of_pullbacks_terminal topos_pullbacks topos_terminal.

(*
   本节说明（余）极限、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p417_finset_terminal_computes :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete_pb)
  = 1%nat := eq_refl.

(* Control: it IS the terminal object up to isomorphism, by uniqueness. *)
Definition p417_finset_terminal_iso :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete_pb)
  ≅ @terminal_obj FinSet FinSet_Terminal :=
  terminal_unique (FinitelyComplete_Terminal FinSet_FinitelyComplete_pb)
                  FinSet_Terminal.

(* The shape [Omega] (Instance/Omega.v) is NOT finite: its identity arrows
   would inject [nat] into [Fin.t n]. *)
Theorem Omega_not_FiniteCategory : FiniteCategory Omega -> False.
Proof.
  intros HJ.
  apply (fin_no_nat_injection (fun n => `1 (fc_cover HJ (@id Omega n)))).
  intros i j e.
  pose proof (hit_dom (`2 (fc_cover HJ (@id Omega i)))) as hi.
  pose proof (hit_dom (`2 (fc_cover HJ (@id Omega j)))) as hj.
  rewrite e in hi.
  exact (eq_trans (eq_sym hi) hj).
Qed.

(* * ** Guards: every 常值 negative names, outside every [Fail] （已译） *)

Check @Terminal.
Check @Cocones.
Check @Opposite.
Check @Colimit_Cocones.
Check @Colimit.
Check @Limit_Cones.
Check @Cones_Limit.
Check @Complete.
Check @FinitelyComplete.
Check @finitely_complete_from_generators.
Check @HasCoequalizers.
Check @Cartesian.
Check @EmptyDiagram_bare.
Check @EmptyDiagram.
Check @EmptyShape.
Check @Limit.
Check @Two_FiniteCategory.
Check @_2.
Check @ArrowIx.
Check @FiniteCategory.
Check nat.
