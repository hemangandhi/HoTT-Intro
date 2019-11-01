Require Export section_06_universes.

(** Section 7.1. Homotopies *)

(** Definition 7.1.1 *)

Definition htpy {A} {B : A -> Type} (f g : forall x, B x) : Type :=
  forall x, f x == g x.

Notation "f '~' g" := (htpy f g) (at level 90).

(** Definition 7.1.2 *)

Definition refl_htpy {A} {B : A -> Type} {f : forall x, B x} : f ~ f :=
  fun x => refl.

Definition concat_htpy {A} {B : A -> Type} {f g h : forall x, B x} :
  f ~ g -> g ~ h -> f ~ h.
Proof.
  intros H K x.
  exact (concat (H x) (K x)).
Defined.

Definition inv_htpy {A} {B : A -> Type} {f g : forall x, B x} :
  f ~ g -> g ~ f.
Proof.
  intros H x.
  exact (inv (H x)).
Defined.

Definition assoc_htpy {A} {B : A -> Type} {f g h k : forall x, B x}
           (H : f ~ g) (K : g ~ h) (L : h ~ k) :
  concat_htpy (concat_htpy H K) L ~ concat_htpy H (concat_htpy K L).
Proof.
  intro x.
  exact (assoc (H x) (K x) (L x)).
Defined.

Definition left_unit_htpy {A} {B : A -> Type} {f g : forall x, B x}
           (H : f ~ g) :
  concat_htpy refl_htpy H ~ H.
Proof.
  intro x.
  exact (left_unit (H x)).
Defined.

Definition right_unit_htpy {A} {B : A -> Type} {f g : forall x, B x}
           (H : f ~ g) :
  concat_htpy H refl_htpy ~ H.
Proof.
  intro x.
  exact (right_unit (H x)).
Defined.

Definition left_inv_htpy {A} {B : A -> Type} {f g : forall x, B x}
           (H : f ~ g) :
  concat_htpy (inv_htpy H) H ~ refl_htpy.
Proof.
  intro x.
  exact (left_inv (H x)).
Defined.

Definition right_inv_htpy {A} {B : A -> Type} {f g : forall x, B x}
           (H : f ~ g) :
  concat_htpy H (inv_htpy H) ~ refl_htpy.
Proof.
  intro x.
  exact (right_inv (H x)).
Defined.

(** Definition 7.1.3 *)

Definition left_whisker_htpy {A B C} (g : B -> C) {f f' : A -> B} (H : f ~ f') :
  comp g f ~ comp g f'.
Proof.
  intro x.
  exact (ap g (H x)).
Defined.

Definition right_whisker_htpy {A B C} {g g' : B ->C} (H : g ~ g') (f : A -> B) :
  comp g f ~ comp g' f.
Proof.
  intro x.
  exact (H (f x)).
Defined.

(** Section 7.2. Bi-invertible maps *)

(** Definition 7.2.1 *)

Definition sec {A B} (f : A -> B) : Type :=
  Sigma (B -> A) (fun g => comp f g ~ idmap).

Definition map_sec {A B} {f : A -> B} (s : sec f) : B -> A := pr1 s.

Definition htpy_sec {A B} {f : A -> B} (s : sec f) :
  comp f (map_sec s) ~ idmap := pr2 s.

Definition retr {A B} (f : A -> B) : Type :=
  Sigma (B -> A) (fun h => comp h f ~ idmap).

Definition map_retr {A B} {f : A -> B} (r : retr f) : B -> A := pr1 r.

Definition htpy_retr {A B} {f : A -> B} (r : retr f) :
  comp (map_retr r) f ~ idmap := pr2 r.

Definition is_equiv {A B} (f : A -> B) : Type :=
  prod (sec f) (retr f).

Definition equiv (A B : Type) : Type := Sigma (A -> B) is_equiv.

Notation "A '<~>' B" := (equiv A B) (at level 70).

Definition map_equiv {A B} (e : A <~> B) : A -> B := pr1 e.

Definition is_equiv_map_equiv {A B} (e : A <~> B) :
  is_equiv (map_equiv e) := pr2 e.

(** Remark 7.2.2 *)

Definition has_inverse {A B} (f : A -> B) : Type :=
  Sigma (B -> A) (fun g => prod (comp f g ~ idmap) (comp g f ~ idmap)).

Definition is_equiv_has_inverse {A B} {f : A -> B} :
  forall (g : B -> A), (comp f g ~ idmap) -> (comp g f ~ idmap) -> is_equiv f.
Proof.
  intros g G H.
  exact (pair (pair g G) (pair g H)).
Defined.

Definition is_equiv_has_inverse' {A B} (f : A -> B) :
  has_inverse f -> is_equiv f.
Proof.
  intro I.
  destruct I as [g [G H]].
  now apply (is_equiv_has_inverse g).
Defined.

(** Lemma 7.2.3 *)

Definition sec_is_equiv {A B} {f : A -> B} (H : is_equiv f) : sec f := pr1 H.

Definition inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) : B -> A :=
  map_sec (sec_is_equiv H).

Definition is_sec_inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  comp f (inv_is_equiv H) ~ idmap := htpy_sec (sec_is_equiv H).

Definition retr_is_equiv {A B} {f : A -> B} (H : is_equiv f) : retr f := pr2 H.

Definition map_retr_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  B -> A := map_retr (retr_is_equiv H).

Definition htpy_retr_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  comp (map_retr_is_equiv H) f ~ idmap := htpy_retr (retr_is_equiv H).

Definition htpy_sec_retr {A B} {f : A -> B} (H : is_equiv f) :
  inv_is_equiv H ~ map_retr_is_equiv H.
Proof.
  intro y.
  transitivity (map_retr_is_equiv H (f (inv_is_equiv H y))).
  - exact (inv (htpy_retr_is_equiv H (inv_is_equiv H y))).
  - exact (ap (map_retr_is_equiv H) (is_sec_inv_is_equiv H y)).
Defined.

Definition is_retr_inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  comp (inv_is_equiv H) f ~ idmap.
Proof.
  intro x.
  transitivity (map_retr_is_equiv H (f x)).
  - exact (htpy_sec_retr H (f x)).
  - exact (htpy_retr_is_equiv H x).
Defined.

Definition has_inverse_is_equiv {A B} {f : A -> B} :
  is_equiv f -> has_inverse f.
Proof.
  intro H.
  apply (pair (inv_is_equiv H)).
  apply pair.
  - exact (is_sec_inv_is_equiv H).
  - exact (is_retr_inv_is_equiv H).
Defined.

(** Corollary 7.2.4 *)

Definition has_inverse_inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  has_inverse (inv_is_equiv H).
Proof.
  apply (pair f).
  apply pair.
  - exact (is_retr_inv_is_equiv H).
  - exact (is_sec_inv_is_equiv H).
Defined.

Definition is_equiv_inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  is_equiv (inv_is_equiv H).
Proof.
  apply is_equiv_has_inverse'.
  apply has_inverse_inv_is_equiv.
Defined.

Definition inv_equiv {A B} : (A <~> B) -> (B <~> A).
Proof.
  intro e.
  apply (pair (inv_is_equiv (is_equiv_map_equiv e))).
  apply is_equiv_inv_is_equiv.
Defined.

(** Remark 7.2.5 *)

Definition is_equiv_idmap {A} : is_equiv (@idmap A).
Proof.
  apply (is_equiv_has_inverse idmap); exact refl_htpy.
Defined.

Definition id_equiv {A} : A <~> A := pair idmap is_equiv_idmap.

(** Example 7.2.6 *)

Definition is_equiv_swap_Pi {A B} (C : A -> B -> Type) :
  is_equiv (@swap_Pi A B C).
Proof.
  apply (is_equiv_has_inverse (@swap_Pi B A (fun y x => C x y)));
    exact refl_htpy.
Defined.

(** Section 7.3. The identity type of a Sigma-type *)

(** Definition 7.3.1 *)

Definition Eq_Sigma {A : Type} {B : A -> Type} (s t : Sigma A B) : Type :=
  Sigma (pr1 s == pr1 t) (fun p => tr B p (pr2 s) == pr2 t).

(** Lemma 7.3.2 *)

Lemma refl_Eq_Sigma {A B} {s : Sigma A B} : Eq_Sigma s s.
Proof.
  exact (pair refl refl).
Defined.

(** Definition 7.3.3 *)

Definition pair_eq {A B} {s t : Sigma A B} (p : s == t) : Eq_Sigma s t.
Proof.
  destruct p.
  exact refl_Eq_Sigma.
Defined.

(** Theorem 7.3.4 *)

Definition eq_pair {A B} {s t : Sigma A B} (p : Eq_Sigma s t) : s == t.
Proof.
  destruct p as [p q].
  destruct s as [x y]; destruct t as [x' y'].
  cbn in p; cbn in q.
  destruct p; destruct q.
  reflexivity.
Defined.

Definition is_sec_eq_pair {A B} {s t : Sigma A B} :
  comp (@pair_eq A B s t) (@eq_pair A B s t) ~ idmap.
Proof.
  intro p.
  destruct p as [p q].
  destruct s as [x y]; destruct t as [x' y'].
  cbn in p; cbn in q.
  destruct p; destruct q.
  reflexivity.
Defined.

Definition is_retr_eq_pair {A B} {s t : Sigma A B} :
  comp (@eq_pair A B s t) (@pair_eq A B s t) ~ idmap.
Proof.
  intro p; destruct p.
  destruct s. reflexivity.
Defined.

Theorem is_equiv_pair_eq {A B} {s t : Sigma A B} :
  is_equiv (@pair_eq A B s t).
Proof.
  apply (is_equiv_has_inverse eq_pair).
  - exact is_sec_eq_pair.
  - exact is_retr_eq_pair.
Defined.

Definition pair_eq_equiv {A B} {s t : Sigma A B} :
  (s == t) <~> Eq_Sigma s t := pair pair_eq is_equiv_pair_eq.

Theorem is_equiv_eq_pair {A B} {s t : Sigma A B} :
  is_equiv (@eq_pair A B s t).
Proof.
  apply (is_equiv_has_inverse pair_eq).
  - exact is_retr_eq_pair.
  - exact is_sec_eq_pair.
Defined.

Definition eq_pair_equiv {A B} {s t : Sigma A B} :
  (Eq_Sigma s t) <~> (s == t) := pair eq_pair is_equiv_eq_pair.

(** Exercises *)

(** Exercise 7.1 *)

Definition inv_inv {A} {x y : A} (p : x == y) : inv (inv p) == p.
Proof.
  now destruct p.
Defined.

Theorem is_equiv_inv {A} {x y} : is_equiv (@inv A x y).
Proof.
  apply (is_equiv_has_inverse inv); exact inv_inv.
Defined.

Definition invmap_equiv {A} {x y : A} : (x == y) <~> (y == x) :=
  pair inv is_equiv_inv.

Theorem is_equiv_concat {A} {x y z : A} (p : x == y) :
  is_equiv (@concat A x y z p).
Proof.
  apply (is_equiv_has_inverse (concat (inv p))); destruct p; exact refl_htpy.
Defined.

Definition concat_equiv {A} {x y z : A} (p : x == y) :
  (y == z) <~> (x == z) :=
  pair (concat p) (is_equiv_concat p).

Theorem is_equiv_concat' {A} {x y z : A} (q : y == z) :
  is_equiv (@concat' A x y z q).
Proof.
  apply (is_equiv_has_inverse (concat' (inv q)));
    destruct q; intro p; now destruct p.
Defined.

Definition concat_equiv' {A} {x y z : A} (q : y == z) :
  (x == y) <~> (x == z) :=
  pair (concat' q) (is_equiv_concat' q).

Theorem is_equiv_tr {A} {B : A -> Type} {x y} (p : x == y) : is_equiv (tr B p).
Proof.
  apply (is_equiv_has_inverse (tr B (inv p))); destruct p; exact refl_htpy.
Defined.

Definition tr_equiv {A} (B : A -> Type) {x y} (p : x == y) :
  B x <~> B y := pair (tr B p) (is_equiv_tr p).

(** Exercise 7.2 *)

Definition inv_inl {X} : coprod X empty -> X.
Proof.
  intro x; now destruct x.
Defined.

Definition is_sec_inv_inl {X} : comp (@inl X empty) (@inv_inl X) ~ idmap.
Proof.
  intro x; now destruct x.
Defined.

Definition is_retr_inv_inl {X} : comp (@inv_inl X) (@inl X empty) ~ idmap.
Proof.
  now intro x.
Defined.

Theorem is_equiv_inl {X} : is_equiv (@inl X empty).
Proof.
  apply (is_equiv_has_inverse (inv_inl)).
  - exact is_sec_inv_inl.
  - exact is_retr_inv_inl.
Defined.

Definition inv_inr {X} : coprod empty X -> X.
Proof.
  intro x; now destruct x.
Defined.

Definition is_sec_inv_inr {X} : comp (@inr empty X) (@inv_inr X) ~ idmap.
Proof.
  intro x; now destruct x.
Defined.

Definition is_retr_inv_inr {X} : comp (@inv_inr X) (@inr empty X) ~ idmap.
Proof.
  now intro x.
Defined.

Theorem is_equiv_inr {X} : is_equiv (@inr empty X).
Proof.
  apply (is_equiv_has_inverse inv_inr).
  - exact is_sec_inv_inr.
  - exact is_retr_inv_inr.
Defined.

Definition inv_pr1_empty {X} : empty -> prod empty X := ex_falso.

Definition is_sec_inv_pr1_empty {X} :
  comp pr1 (@inv_pr1_empty X) ~ idmap := ex_falso.

Definition is_retr_inv_pr1_empty {X} :
  comp (@inv_pr1_empty X) pr1 ~ idmap.
Proof.
  intro x; now destruct x.
Defined.

Theorem is_equiv_pr1_empty {X} : is_equiv (@pr1 empty (fun t => X)).
Proof.
  apply (is_equiv_has_inverse (inv_pr1_empty)).
  - exact is_sec_inv_pr1_empty.
  - exact is_retr_inv_pr1_empty.
Defined.

Definition inv_pr2_empty {X} : empty -> prod X empty := ex_falso.

Definition is_sec_inv_pr2_empty {X} :
  comp (@pr2 X (const empty)) (@inv_pr2_empty X) ~ idmap := ex_falso.

Definition is_retr_inv_pr2_empty {X} :
  comp (@inv_pr2_empty X) (@pr2 X (const empty)) ~ idmap.
Proof.
  intro x. now destruct x.
Defined.

Theorem is_equiv_pr2_empty {X} : is_equiv (@pr2 X (const empty)).
Proof.
  apply (is_equiv_has_inverse inv_pr2_empty).
  - exact is_sec_inv_pr2_empty.
  - exact is_retr_inv_pr2_empty.
Defined.

(** Exercise 7.3 *)

(** Exercise 7.3.a *)

Definition is_sec_inv_is_equiv_htpy {A B} {f g : A -> B} (H : f ~ g)
           (is_equiv_g : is_equiv g) :
  comp f (inv_is_equiv is_equiv_g) ~ idmap :=
  concat_htpy
    (right_whisker_htpy H (inv_is_equiv is_equiv_g))
    (is_sec_inv_is_equiv is_equiv_g).

Definition is_retr_inv_is_equiv_htpy {A B} {f g : A -> B} (H : f ~ g)
           (is_equiv_g : is_equiv g) :
  comp (inv_is_equiv is_equiv_g) f ~ idmap :=
  concat_htpy
    (left_whisker_htpy (inv_is_equiv is_equiv_g) H)
    (is_retr_inv_is_equiv is_equiv_g).

Theorem is_equiv_htpy {A B} {f g : A -> B} (H : f ~ g) :
  is_equiv g -> is_equiv f.
Proof.
  intro is_equiv_g.
  apply (is_equiv_has_inverse (inv_is_equiv is_equiv_g)).
  - exact (is_sec_inv_is_equiv_htpy H is_equiv_g).
  - exact (is_retr_inv_is_equiv_htpy H is_equiv_g).
Defined.

Definition is_equiv_htpy' {A B} {f g : A -> B} (H : f ~ g) :
  is_equiv f -> is_equiv g := is_equiv_htpy (inv_htpy H).

(** Exercise 7.3.b *)

Definition htpy_equiv {A B} (e e' : A <~> B) : Type :=
  map_equiv e ~ map_equiv e'.

Definition htpy_inv_equiv {A B} {e e' : A <~> B} :
  htpy_equiv e e' -> htpy_equiv (inv_equiv e) (inv_equiv e').
Proof.
  intros H y.
  transitivity
    (map_equiv (inv_equiv e') (map_equiv e' (map_equiv (inv_equiv e) y))).
  - apply inv. apply (is_retr_inv_is_equiv (is_equiv_map_equiv e')).
  - transitivity
      (map_equiv (inv_equiv e') (map_equiv e (map_equiv (inv_equiv e) y))).
    * apply inv.
      apply (ap (map_equiv (inv_equiv e'))).
      apply H.
    * apply (ap (map_equiv (inv_equiv e'))).
      apply (is_sec_inv_is_equiv (is_equiv_map_equiv e)).
Defined.