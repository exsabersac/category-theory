Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.
Require Import Category.Construction.Funny.Unitors.
Require Import Category.Construction.Funny.Associator.
Require Import Category.Instance.StrictCat.Funny.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Binoidal.

Generalizable All Variables.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record StrictPremonoidal (c : Category) : Type := {
  sp_tensor : (c □ c) ⟶ c;
  sp_unit   : _1 ⟶ c;

  (* 相关说明。 （已译） *)
  sp_unit_left :
    @equiv _ (@Functor_StrictEq_Setoid (_1 □ c) c)
      (sp_tensor ◯ FunnyBimap sp_unit Id[c])
      (to (@Funny_unit_left c));

  (* 相关说明。 （已译） *)
  sp_unit_right :
    @equiv _ (@Functor_StrictEq_Setoid (c □ _1) c)
      (sp_tensor ◯ FunnyBimap Id[c] sp_unit)
      (to (@Funny_unit_right c));

  (* 相关说明。 （已译） *)
  sp_assoc :
    @equiv _ (@Functor_StrictEq_Setoid ((c □ c) □ c) c)
      (sp_tensor ◯ FunnyBimap sp_tensor Id[c])
      ((sp_tensor ◯ FunnyBimap Id[c] sp_tensor) ◯ to (@Funny_assoc c c c))
}.

Arguments sp_tensor {c} _.
Arguments sp_unit {c} _.
Arguments sp_unit_left {c} _.
Arguments sp_unit_right {c} _.
Arguments sp_assoc {c} _.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition StrictPremonoidal_of_Monoid {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) : StrictPremonoidal c :=
  @Build_StrictPremonoidal c
    mappend[m]
    mempty[m]
    (@mempty_left StrictCat Funny_Monoidal c m)
    (@mempty_right StrictCat Funny_Monoidal c m)
    (@mappend_assoc StrictCat Funny_Monoidal c m).

Definition Monoid_of_StrictPremonoidal {c : Category}
  (p : StrictPremonoidal c) : @MonoidObject StrictCat Funny_Monoidal c :=
  @Build_MonoidObject StrictCat Funny_Monoidal c
    (sp_unit p)
    (sp_tensor p)
    (sp_unit_left p)
    (sp_unit_right p)
    (sp_assoc p).

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma roundtrip_monoid {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) :
  Monoid_of_StrictPremonoidal (StrictPremonoidal_of_Monoid m) = m.
Proof. reflexivity. Qed.

Lemma roundtrip_strict_premonoidal {c : Category} (p : StrictPremonoidal c) :
  StrictPremonoidal_of_Monoid (Monoid_of_StrictPremonoidal p) = p.
Proof. reflexivity. Qed.

Lemma roundtrip_mempty {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) :
  mempty[Monoid_of_StrictPremonoidal (StrictPremonoidal_of_Monoid m)]
    = mempty[m].
Proof. reflexivity. Qed.

Lemma roundtrip_mappend {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) :
  mappend[Monoid_of_StrictPremonoidal (StrictPremonoidal_of_Monoid m)]
    = mappend[m].
Proof. reflexivity. Qed.

Lemma roundtrip_sp_unit {c : Category} (p : StrictPremonoidal c) :
  sp_unit (StrictPremonoidal_of_Monoid (Monoid_of_StrictPremonoidal p))
    = sp_unit p.
Proof. reflexivity. Qed.

Lemma roundtrip_sp_tensor {c : Category} (p : StrictPremonoidal c) :
  sp_tensor (StrictPremonoidal_of_Monoid (Monoid_of_StrictPremonoidal p))
    = sp_tensor p.
Proof. reflexivity. Qed.

(*
   本节说明 Premonoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary StrictPremonoidal_unit_left_obj {c : Category}
  (p : StrictPremonoidal c) (x : c) :
  fobj[sp_tensor p] (fobj[sp_unit p] ttt, x) = x.
Proof. exact (`1 (sp_unit_left p) (ttt, x)). Qed.

Corollary StrictPremonoidal_unit_right_obj {c : Category}
  (p : StrictPremonoidal c) (x : c) :
  fobj[sp_tensor p] (x, fobj[sp_unit p] ttt) = x.
Proof. exact (`1 (sp_unit_right p) (x, ttt)). Qed.

Corollary StrictPremonoidal_assoc_obj {c : Category}
  (p : StrictPremonoidal c) (x y z : c) :
  fobj[sp_tensor p] (fobj[sp_tensor p] (x, y), z)
    = fobj[sp_tensor p] (x, fobj[sp_tensor p] (y, z)).
Proof. exact (`1 (sp_assoc p) ((x, y), z)). Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition StrictPremonoidal_Binoidal {c : Category}
  (p : StrictPremonoidal c) : @Binoidal c :=
  @Build_Binoidal c
    (fun x y : c => fobj[sp_tensor p] (x, y))
    (fun y' : c => ToAFunctor (sp_tensor p ◯ @FunnyL c c y'))
    (fun x' : c => ToAFunctor (sp_tensor p ◯ @FunnyR c c x')).

(* The extracted tensor 对象 action multiplication, the
 nose. （已译） *)
Corollary StrictPremonoidal_Binoidal_tensor {c : Category}
  (p : StrictPremonoidal c) (x y : c) :
  @tensor c (StrictPremonoidal_Binoidal p) x y = fobj[sp_tensor p] (x, y).
Proof. reflexivity. Qed.

(* The two partial tensoring 函子 act 态射 multiplication
 acts generating steps funny tensor — definitionally. （已译） *)
Corollary StrictPremonoidal_inj_left_fmap {c : Category}
  (p : StrictPremonoidal c) {x y : c} (f : x ~{c}~> y) (y' : c) :
  fmap[@inj_left c (StrictPremonoidal_Binoidal p) y'] f
    = @fmap (c □ c) c (sp_tensor p) (x, y') (y, y') (lstep f).
Proof. reflexivity. Qed.

Corollary StrictPremonoidal_inj_right_fmap {c : Category}
  (p : StrictPremonoidal c) (x' : c) {x y : c} (f : x ~{c}~> y) :
  fmap[@inj_right c (StrictPremonoidal_Binoidal p) x'] f
    = @fmap (c □ c) c (sp_tensor p) (x', x) (x', y) (rstep f).
Proof. reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition StrictPremonoidal_SepFunctorial {c : Category}
  (p : StrictPremonoidal c) :
  @SepFunctorial c c c (fun x y : c => fobj[sp_tensor p] (x, y)) :=
  toSep (sp_tensor p).

(* 相关说明。 （已译） *)
Corollary StrictPremonoidal_sf_lmap {c : Category}
  (p : StrictPremonoidal c) {x y : c} (f : x ~{c}~> y) (d : c) :
  sf_lmap (StrictPremonoidal_SepFunctorial p) f d
    = @fmap (c □ c) c (sp_tensor p) (x, d) (y, d) (lstep f).
Proof. reflexivity. Qed.

Corollary StrictPremonoidal_sf_rmap {c : Category}
  (p : StrictPremonoidal c) (x : c) {d d' : c} (g : d ~{c}~> d') :
  sf_rmap (StrictPremonoidal_SepFunctorial p) x g
    = @fmap (c □ c) c (sp_tensor p) (x, d) (x, d') (rstep g).
Proof. reflexivity. Qed.
