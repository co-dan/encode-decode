Require Import HoTT.
Require Import ED.polynomial.
Require Import ED.hit_structure.

(** A groupoid consists of a relation with a certain structure.
   This relation has two parts.
   First of all, it has objects.
   Second of all, for each pair of objects there is a set of arrows between them.
*)
Definition relation (A : Type) := A -> A -> hSet.

(** Now we can define what a groupoid is.
    In addition to a relation, we also have algebraic structure.
*)
Record groupoid (A : Type) :=
  Build_grpd { hom : relation A ;
               e : forall (x : A), hom x x ;
               inv : forall (x y : A), hom x y -> hom y x ;
               comp : forall (x y z : A), hom x y -> hom y z -> hom x z ;
               ca : forall (x y z v : A) (p : hom x y) (q : hom y z) (r : hom z v),
                   comp _ _ _ p (comp _ _ _ q r) = comp _ _ _ (comp _ _ _ p q) r ;
               ce : forall (x y : A) (p : hom x y), comp x y y p (e y) = p ;
               ec : forall (x y : A) (p : hom x y), comp x x y (e x) p = p ;
               ci : forall (x y : A) (p : hom x y), comp x y x p (inv x y p) = e x ;
               ic : forall (x y : A) (p : hom x y), comp y x y (inv x y p) p = e y ;
             }.

Arguments e {_} {_} _.
Arguments hom {_} _.
Arguments inv {_} {_} {_} {_}.
Notation "p × q" := (comp _ _ _ _ _ p q) (at level 80).

(** Now let's discuss some examples of groupoids.
    The first example is the paths on a certain type.
*)
Definition path_space (X : Type) : X -> X -> hSet
  := fun (x y : X) => BuildhSet (Trunc 0 (x = y)).

Definition path_groupoid (X : Type) : groupoid X.
Proof.
  unshelve esplit ; simpl.
  - exact (path_space X).
  - exact (fun _ => tr idpath).
  - exact (fun _ _ => Trunc_rec (fun p => tr p^)).
  - exact (fun _ _ _ p' q' => Trunc_rec (fun p => Trunc_rec (fun q => tr (p @ q)) q') p').
  - intros ? ? ? ? p q r ; simpl.
    strip_truncations ; simpl.
    exact (ap tr (concat_p_pp p q r)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_p1 p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_1p p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_pV p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_Vp p)).
Defined.

Notation "p · q" := (comp _ (path_groupoid _) _ _ _ p q) (at level 80).

(** Groupoids are closed under products. *)
Definition prod_groupoid
           (A B : Type) (G₁ : groupoid A) (G₂ : groupoid B)
  : groupoid (A * B).
Proof.
  unshelve esplit.
  - exact (fun x y => BuildhSet (hom G₁ (fst x) (fst y) * hom G₂ (snd x) (snd y))).
  - intros ; simpl.
    split ; apply e.
  - intros ? ? [p1 p2] ; simpl.
    exact (inv p1, inv p2).
  - intros ? ? ? [p1 p2] [q1 q2].
    exact (p1 × q1, p2 × q2).
  - intros ? ? ? ? [p1 p2] [q1 q2] [r1 r2].
    apply path_prod ; apply ca.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ce.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ec.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ci.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ic.
Defined.

(** Groupoids are closed under sums. *)
Definition sum_groupoid
           (A B : Type) (G₁ : groupoid A) (G₂ : groupoid B)
  : groupoid (A + B).
Proof.
  unshelve esplit.
  - exact (fun x y =>
             match x, y with
             | inl x, inl y => hom G₁ x y
             | inl _, inr _ => BuildhSet Empty
             | inr _, inl _ => BuildhSet Empty
             | inr x, inr y => hom G₂ x y
             end).
  - intros [x | x] ; apply e.
  - intros [? | ?] [? | ?] ; contradiction || apply inv.
  - intros [? | ?] [? | ?] [? | ?] ; contradiction || apply comp.
  - intros [? | ?] [? | ?] [? | ?] [? | ?] ; try contradiction ; apply ca.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ce.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ec.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ci.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ic.
Defined.    

(** We can apply polynomial functors to groupoids. *)
Definition lift_groupoid
           {A : Type} (G : groupoid A) (P : polynomial)
  : groupoid (poly_act P A).
Proof.
  induction P ; simpl.
  - exact G.
  - exact (path_groupoid T).
  - apply prod_groupoid ; assumption.
  - apply sum_groupoid ; assumption.
Defined.

(** To give specifications for these constructions, we need to define morphisms of groupoids.
    For that, we first define morphisms of relations.
    These come in two kinds: the underlying type could be the same or we have a map between them.
*)
Definition relation_morph
           {A B : Type}
           (f : A -> B)
           (R₁ : relation A) (R₂ : relation B)
  := forall (x y : A), R₁ x y -> R₂ (f x) (f y).

(** A groupoid morphism is a relation morphism which preserves the algebraic structure. *)
Class is_grpd_morph
      {A B : Type}
      (f : A -> B)
      {G₁ : groupoid A} {G₂ : groupoid B}
      (map : relation_morph f (hom G₁) (hom G₂))
  := { morph_e : forall (x : A), map _ _ (e x) = e (f x) ;
       morph_i : forall (x y : A) (p : hom G₁ x y),
           map _ _ (inv p) = inv (map _ _ p) ;
       morph_c : forall (x y z : A) (p : hom G₁ x y) (q : hom G₁ y z),
           map x z (p × q) = (map x y p × map y z q)
     }.

Class is_Agrpd_morph
      {A : Type}
      {G₁ G₂ : groupoid A}
      (Amap : relation_morph idmap (hom G₁) (hom G₂))
  := is_idd_Agrpd_morph : is_grpd_morph idmap Amap.

Global Instance to_grpd_morph
       {A : Type}
       {G₁ G₂ : groupoid A}
       (Amap : relation_morph idmap (hom G₁) (hom G₂))
       `{is_Agrpd_morph _ _ _ Amap}
  : is_grpd_morph idmap Amap.
Proof.
  assumption.
Defined.

Arguments morph_e {_} {_} _ {_} {_} _ {_} _.
Arguments morph_i {_} {_} _ {_} {_} _ {_} _ _ _.
Arguments morph_c {_} {_} _ {_} {_} _ {_} _ _ _ _ _.

Definition grpd_morph
           {A B : Type}
           (f : A -> B)
           (G₁ : groupoid A) (G₂ : groupoid B)
  := {map : relation_morph f (hom G₁) (hom G₂) & merely (is_grpd_morph f map)}.

Definition Agrpd_morph
           {A : Type}
           (G₁ G₂ : groupoid A)
  := grpd_morph idmap G₁ G₂.

Coercion WATER
         {A B : Type}
         (f : A -> B)
         (G₁ : groupoid A) (G₂ : groupoid B)
  := fun (x : grpd_morph f G₁ G₂) => x.1.

Definition BuildAGrpdMorph {A : Type} (G₁ G₂ : groupoid A)
  (f : relation_morph idmap (hom G₁) (hom G₂)) `{is_Agrpd_morph _ _ _ f}
  : Agrpd_morph G₁ G₂
  := (f;tr _).

(** We need the identity. *)
Global Instance id_is_Agrpd_morph {A : Type} (G₁ : groupoid A)
  : @is_Agrpd_morph A G₁ G₁ (fun _ _ => idmap).
Proof.
  esplit; reflexivity.
Defined.

Definition id_Agrpd {A : Type} (G₁ : groupoid A) : Agrpd_morph G₁ G₁
  := BuildAGrpdMorph _ _ (fun _ _ => idmap).

(** Now we show lifting is functorial. *)
Definition sum_func
           {A B : Type}
           (G₁ : groupoid A) (G₂ : groupoid B)
           (G₃ : groupoid A) (G₄ : groupoid B)
           (F₁ : Agrpd_morph G₁ G₃) (F₂ : Agrpd_morph G₂ G₄)
  : Agrpd_morph (sum_groupoid _ _ G₁ G₂) (sum_groupoid _ _ G₃ G₄).
Proof.
  unshelve eexists.
  - intros [x | x] [y | y] p ; try contradiction.
    * exact (F₁.1 _ _ p).
    * exact (F₂.1 _ _ p).
  - apply tr.
    unshelve eexists.
    + intros [x | x] ; simpl.
      * simple refine (Trunc_rec _ (F₁.2)).
        intros H.
        apply H.
      * simple refine (Trunc_rec _ (F₂.2)).
        intros H.
        apply H.
    + intros [x | x] [y | y] p ; try contradiction ; simpl.
      * simple refine (Trunc_rec _ (F₁.2)).
        intros H.
        apply H.
      * simple refine (Trunc_rec _ (F₂.2)).
        intros H.
        apply H.
    + intros [x | x] [y | y] [z | z] p q ; try contradiction ; simpl.
      * simple refine (Trunc_rec _ (F₁.2)).
        intros H.
        apply H.
      * simple refine (Trunc_rec _ (F₂.2)).
        intros H.
        apply H.
Defined.

Definition prod_func
           {A B : Type}
           (G₁ : groupoid A) (G₂ : groupoid B)
           (G₃ : groupoid A) (G₄ : groupoid B)
           (F₁ : Agrpd_morph G₁ G₃) (F₂ : Agrpd_morph G₂ G₄)
  : Agrpd_morph (prod_groupoid _ _ G₁ G₂) (prod_groupoid _ _ G₃ G₄).
Proof.
  unshelve eexists.
  - intros [x1 x2] [y1 y2] p.
    split.
    * exact (F₁.1 _ _ (fst p)).
    * exact (F₂.1 _ _ (snd p)).
  - apply tr.
    unshelve eexists.
    + intros [x1 x2] ; simpl.
      apply path_prod'.
      * simple refine (Trunc_rec _ (F₁.2)).
        intros H.
        apply H.
      * simple refine (Trunc_rec _ (F₂.2)).
        intros H.
        apply H.
    + intros [x1 x2] [y1 y2] p ; simpl.
      apply path_prod'.
      * simple refine (Trunc_rec _ (F₁.2)).
        intro H.
        apply H.
      * simple refine (Trunc_rec _ (F₂.2)).
        intros H.
        apply H.
    + intros [x1 x2] [y1 y2] [z1 z2] p q ; simpl.
      apply path_prod'.
      * simple refine (Trunc_rec _ (F₁.2)).
        intros H.
        apply H.
      * simple refine (Trunc_rec _ (F₂.2)).
        intros H.
        apply H.
Defined.

Definition poly_func
           {A : Type}
           (P : polynomial)
           (G₁ G₂ : groupoid A)
           (F₁ : Agrpd_morph G₁ G₂)
  : Agrpd_morph (lift_groupoid G₁ P) (lift_groupoid G₂ P).
Proof.
  induction P ; simpl.
  - exact F₁.
  - apply id_Agrpd.
  - apply prod_func ; assumption.
  - apply sum_func ; assumption.
Defined.    

(** Now we suppose that we are given a HIT.
    We define a class of groupoids with the same structure as the path space of that HIT.
*)
Section H_alg.
  Variable (Σ : hit_signature) (H : HIT Σ).

  (** First of all, we have the `ap` operation on paths.
      This gives an algebra structure using the lifted groupoid.
   *)
  (** For every constuctor `C_i : P_i[H] -> H` of `H`, require a morphism
        P_i[G] -> G
      which lies over `C_i`.
   *)
  Definition hit_point_morph (G : groupoid H) (i : sig_point_index Σ) :=
    grpd_morph
      (hit_point i)
      (lift_groupoid G (sig_point Σ i))
      G.
  
  Definition P_alg (G : groupoid H) : Type
    := forall (i : sig_point_index Σ), hit_point_morph G i.

  (** Second of all, we need to have the path constructors. *)
  Definition contains
             {A B : Type}
             (G : groupoid B)
             (f g : A -> B)
    := forall (x : A), hom G (f x) (g x).

  (** Lastly, we need a coherency.
      The path constructors can be obtained in two ways.
      Either we can use `contains` or we can use `transport`.
   *)
  Definition coherent
             (j : sig_path_index Σ)
             (G : groupoid H)
             (Gpath : contains G
                   (endpoint_act hit_point (sig_path_lhs Σ j))
                   (endpoint_act hit_point (sig_path_rhs Σ j)))
    : Type
    := forall (u : poly_act (sig_path_param Σ j) H),
      Gpath u = transport (fun z => hom G _ z) (hit_path j u) (e _).
    
  (** Now we can define the structure of the path space. *)
  Record Halg :=
    { H_grpd : groupoid H ;
      point_alg : P_alg H_grpd ;
      path_alg : forall (j : sig_path_index Σ),
          contains H_grpd
                   (endpoint_act hit_point (sig_path_lhs Σ j))
                   (endpoint_act hit_point (sig_path_rhs Σ j)) ;
      coherent_alg : forall (j : sig_path_index Σ),
          coherent j H_grpd (path_alg j)
    }.

  (** For the morphisms, we have multiple requirements. *)
  Definition preserves_alg {G₁ G₂ : Halg} (F : Agrpd_morph (H_grpd G₁) (H_grpd G₂))
    : Type
    := forall (i : sig_point_index Σ)
              (a₁ a₂ : poly_act (sig_point Σ i) H)
              (x : hom (lift_groupoid (H_grpd G₁) (sig_point Σ i)) a₁ a₂),
      F.1 _ _ ((point_alg G₁ i).1 _ _ x)
      =
      (point_alg G₂ i).1
                      _
                      _
                      ((poly_func (sig_point Σ i) (H_grpd G₁) (H_grpd G₂) F).1 _ _ x).    
  
  Definition preserves_paths {G₁ G₂ : Halg} (F : Agrpd_morph (H_grpd G₁) (H_grpd G₂))
    : Type
    := forall (j : sig_path_index Σ) (u : poly_act (sig_path_param Σ j) H),
      path_alg G₂ j u = F.1 _ _ (path_alg G₁ j u).

  Class isHalg_morph (G₁ G₂ : Halg) (F : Agrpd_morph (H_grpd G₁) (H_grpd G₂))
    := { p_alg : preserves_alg F ;
         p_paths : preserves_paths F}.
End H_alg.