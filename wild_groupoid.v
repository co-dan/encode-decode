Require Import HoTT.
Require Import ED.polynomial.
Require Import ED.hit_structure.

(** A groupoid consists of a relation with a certain structure.
   This relation has two parts.
   First of all, it has objects.
   Second of all, for each pair of objects there is a set of arrows between them.
*)
Definition relation (A : Type) := A -> A -> Type.

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
Definition path_space (X : Type) : relation X
  := fun (x y : X) => x = y.

Definition path_groupoid (X : Type) : groupoid X.
Proof.
  unshelve esplit ; simpl.
  - exact (path_space X).
  - exact (fun _ => idpath).
  - exact (fun _ _ => fun p => p^).
  - exact (fun _ _ _ p q => p @ q).
  - intros ; apply concat_p_pp.
  - intros ; apply concat_p1.
  - intros ; apply concat_1p.
  - intros ; apply concat_pV.
  - intros ; apply concat_Vp.
Defined.

(** Groupoids are closed under products. *)
Definition prod_groupoid
           (A B : Type) (G₁ : groupoid A) (G₂ : groupoid B)
  : groupoid (A * B).
Proof.
  unshelve esplit.
  - exact (fun x y => hom G₁ (fst x) (fst y) * hom G₂ (snd x) (snd y)).
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
             | inl _, inr _ => Empty
             | inr _, inl _ => Empty
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

(** We need the identity. *)
Definition id_relation_morph {A : Type} (G₁ : groupoid A)
  : relation_morph idmap (hom G₁) (hom G₁)
  := fun _ _ => idmap.

Global Instance id_is_Agrpd_morph {A : Type} (G₁ : groupoid A)
  : @is_Agrpd_morph A G₁ G₁ (id_relation_morph G₁).
Proof.
  esplit; reflexivity.
Defined.

(** Now we show lifting is functorial. *)
Definition sum_func
           {A B : Type}
           (G₁ : groupoid A) (G₂ : groupoid B)
           (G₃ : groupoid A) (G₄ : groupoid B)
           (F₁ : relation_morph idmap (hom G₁) (hom G₃))
           (F₂ : relation_morph idmap (hom G₂) (hom G₄))
  : relation_morph idmap (hom (sum_groupoid _ _ G₁ G₂)) (hom (sum_groupoid _ _ G₃ G₄)).
Proof.
  intros [x | x] [y | y] p ; try contradiction.
  * exact (F₁ _ _ p).
  * exact (F₂ _ _ p).
Defined.

Global Instance sum_func_grpd
           {A B : Type}
           (G₁ : groupoid A) (G₂ : groupoid B)
           (G₃ : groupoid A) (G₄ : groupoid B)
           (F₁ : relation_morph idmap (hom G₁) (hom G₃))
           (F₂ : relation_morph idmap (hom G₂) (hom G₄))
           `{is_Agrpd_morph _ _ _ F₁}
           `{is_Agrpd_morph _ _ _ F₂}
  : is_Agrpd_morph (sum_func _ _ _ _ F₁ F₂).
Proof.
  unshelve eexists.
  + intros [x | x] ; simpl.
    * exact (morph_e _ F₁ _).
    * exact (morph_e _ F₂ _).
  + intros [x | x] [y | y] p ; try contradiction ; simpl.
    * exact (morph_i _ F₁ _ _ _).
    * exact (morph_i _ F₂ _ _ _).
  + intros [x | x] [y | y] [z | z] p q ; try contradiction ; simpl.
    * exact (morph_c _ F₁ _ _ _ _ _).
    * exact (morph_c _ F₂ _ _ _ _ _).
Defined.

Definition prod_func
           {A B : Type}
           (G₁ : groupoid A) (G₂ : groupoid B)
           (G₃ : groupoid A) (G₄ : groupoid B)
           (F₁ : relation_morph idmap (hom G₁) (hom G₃))
           (F₂ : relation_morph idmap (hom G₂) (hom G₄))
  : relation_morph idmap (hom (prod_groupoid _ _ G₁ G₂)) (hom (prod_groupoid _ _ G₃ G₄)).
Proof.
  intros [x1 x2] [y1 y2] p.
  split.
  * exact (F₁ _ _ (fst p)).
  * exact (F₂ _ _ (snd p)).
Defined.

Global Instance prod_func_grpd
       {A B : Type}
       (G₁ : groupoid A) (G₂ : groupoid B)
       (G₃ : groupoid A) (G₄ : groupoid B)
       (F₁ : relation_morph idmap (hom G₁) (hom G₃))
       (F₂ : relation_morph idmap (hom G₂) (hom G₄))
       `{is_Agrpd_morph _ _ _ F₁}
       `{is_Agrpd_morph _ _ _ F₂}
  : is_Agrpd_morph (prod_func _ _ _ _ F₁ F₂).
Proof.
  unshelve eexists.
  + intros [x1 x2] ; simpl.
    apply path_prod'.
    * exact (morph_e _ F₁ _).
    * exact (morph_e _ F₂ _).
  + intros [x1 x2] [y1 y2] p ; simpl.
    apply path_prod'.
    * exact (morph_i _ F₁ _ _ _).
    * exact (morph_i _ F₂ _ _ _).
  + intros [x1 x2] [y1 y2] [z1 z2] p q ; simpl.
    apply path_prod'.
    * exact (morph_c _ F₁ _ _ _ _ _).
    * exact (morph_c _ F₂ _ _ _ _ _).
Defined.

Definition poly_func
           {A : Type}
           (P : polynomial)
           (G₁ G₂ : groupoid A)
           (F₁ : relation_morph idmap (hom G₁) (hom G₂))
  : relation_morph idmap (hom (lift_groupoid G₁ P)) (hom (lift_groupoid G₂ P)).
Proof.
  induction P ; simpl.
  - exact F₁.
  - apply (id_relation_morph (path_groupoid T)).
  - apply prod_func ; assumption.
  - apply sum_func ; assumption.
Defined.

Global Instance poly_func_grpd
       {A : Type}
       (P : polynomial)
       (G₁ G₂ : groupoid A)
       (F₁ : relation_morph idmap (hom G₁) (hom G₂))
       `{is_Agrpd_morph _ _ _ F₁}
  : is_Agrpd_morph (poly_func P G₁ G₂ F₁).
Proof.
  induction P ; apply _.
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
    relation_morph
      (hit_point i)
      (hom (lift_groupoid G (sig_point Σ i)))
      (hom G).
  
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
      point_alg_grpd :
        forall (i : sig_point_index Σ),
          is_grpd_morph (hit_point i) (point_alg i);
      path_alg : forall (j : sig_path_index Σ),
          contains H_grpd
                   (endpoint_act hit_point (sig_path_lhs Σ j))
                   (endpoint_act hit_point (sig_path_rhs Σ j)) ;
      coherent_alg : forall (j : sig_path_index Σ),
          coherent j H_grpd (path_alg j)
    }.

  (** For the morphisms, we have multiple requirements. *)
  Definition preserves_alg
             {G₁ G₂ : Halg}
             (F : relation_morph idmap (hom (H_grpd G₁)) (hom (H_grpd G₂)))
    : Type
    := forall (i : sig_point_index Σ)
              (a₁ a₂ : poly_act (sig_point Σ i) H)
              (x : hom (lift_groupoid (H_grpd G₁) (sig_point Σ i)) a₁ a₂),
      F _ _ ((point_alg G₁ i) _ _ x)
      =
      (point_alg G₂ i)
        _
        _
        ((poly_func (sig_point Σ i) (H_grpd G₁) (H_grpd G₂) F) _ _ x).    
  
  Definition preserves_paths
             {G₁ G₂ : Halg}
             (F : relation_morph idmap (hom (H_grpd G₁)) (hom (H_grpd G₂)))
    : Type
    := forall (j : sig_path_index Σ) (u : poly_act (sig_path_param Σ j) H),
      path_alg G₂ j u = F _ _ (path_alg G₁ j u).

  Class isHalg_morph
        (G₁ G₂ : Halg)
        (F : relation_morph idmap (hom (H_grpd G₁)) (hom (H_grpd G₂)))
    := { p_alg : preserves_alg F ;
         p_paths : preserves_paths F}.
End H_alg.