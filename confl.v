Definition Rel (A:Type) := A -> A -> Prop.

Inductive trans {A} (red: Rel A) : Rel A :=
| singl: forall a b,  red a b -> trans red a b
| transit: forall b a c,  red a b -> trans red b c -> trans red a c
.

Inductive refltrans {A} (red: Rel A) : Rel A :=
| refl: forall a, (refltrans red) a a
| rtrans: forall a b c, red a b -> refltrans red b c -> refltrans red a c
.

Lemma ttrans {A}: forall a b c (red: Rel A), refltrans red a b ->  refltrans red b c -> refltrans red a c. 
Proof.
  Admitted.

Inductive refltrans' {A} (red: Rel A) : Rel A :=
| refl': forall a, (refltrans' red) a a
| rtrans': forall a b c, refltrans' red a b -> red b c -> refltrans' red a c
.

Variable A:Type.
Variable R : Rel A.
Notation "a --> b" := (R a b) (at level 60).
Notation "a -->* b" := ((refltrans R) a b) (at level 60).
Notation "a -->** b" := ((refltrans' R) a b) (at level 60).

Lemma strip_lemma: forall t t1 t2, t --> t1 /\ t -->* t2 -> exists t3, t1 -->* t3 /\ t2 -->* t3.
Proof.
  Admitted.
  
Theorem confl: forall t t1 t2, t -->* t1 /\ t -->* t2 -> exists t3, t1 -->* t3 /\ t2 -->* t3.
Proof.
  intros t t1 t2 H.
  destruct H as [H1 H2].
  generalize dependent t2.
  induction H1.
  - intros t2 H2.
    exists t2. split.
    + assumption.
    + apply refl.
  - intros t2 H2.
    assert (Hstrip: a --> b /\ a -->* t2 -> exists t3, b -->* t3 /\ t2 -->* t3).
    {
      apply strip_lemma.
    }
    assert (Hand: a --> b /\ a -->* t2).
    {
      split.
      - assumption.
      - assumption.
    }
    apply Hstrip in Hand.
    destruct Hand as [t3' [Hb Ht2]].
    apply IHrefltrans in Hb.
    destruct Hb  as[t3 [Hc Ht3']].
    exists t3. split.
    + assumption.
    + apply ttrans with t3'.
      * assumption.
      * assumption.
Qed.

Theorem confl': forall t t1 t2, t -->** t1 /\ t -->** t2 -> exists t3, t1 -->** t3 /\ t2 -->** t3.
Proof.
  Admitted.

Theorem id_p: forall P, P -> P.
Proof.
  intros P.
  intros P1.
  assumption.
Qed.

Lemma id_PP: forall P, (P -> P) -> (P -> P).
Proof.
  intros P p1 p2.
  assumption.
Qed.

Lemma imp_trans: forall P Q R, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P.
  intros Q.
  intros R.
  intros func1.
  intros func2.
  intros Papp.
  pose (Qapp := func1 Papp).
  pose (Rapp := func2 Qapp).
  assumption.
Qed.

Lemma imp_trans_ref: forall P Q R, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P.
  intros Q.
  intros R.
  intros func1.
  intros func2.
  intros Papp.
  refine (func2 _).
  refine (func1 _).
  assumption.
Qed.

Lemma imp_perm : forall P Q R, (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros P Q R.
  intros func1.
  intros Qapp.
  intros Papp.
  pose (QRapp := func1 Papp).
  pose (Rapp := QRapp Qapp).
  assumption.
Qed.

Lemma ignore_Q : forall P Q R, (P -> R) -> P -> Q -> R.
Proof.
  intros P Q R.
  intros func1.
  intros Papp.
  intros Qapp.
  pose (Rapp := func1 Papp).
  assumption.
Qed.

Lemma ignore_Q_without_parenthesis : forall P Q R, P -> R -> P -> Q -> R.
Proof.
  intros P Q R.
  intros Papp Rapp Papp2 Qapp1.
  assumption.
Qed.

Lemma delta_imp : forall P Q, (P -> P -> Q) -> P -> Q.
Proof.
  intros P Q.
  intros func1.
  intros Papp.
  pose (PQapp := func1 Papp).
  pose (Qapp := PQapp Papp).
  assumption.
Qed.

Lemma delta_impR : forall P Q, (P->Q)->(P->P->Q).
Proof.
  intros P Q.
  intros func1.
  intros Papp.
  intros Papp2.
  pose (Qapp := func1 Papp).
  assumption.
Qed.

Lemma diamond : forall P Q R T, (P->Q)->(P->R)->(Q->R->T)->P->T.
Proof.
  intros P Q R T.
  intros func1.
  intros func2.
  intros func3.
  intros Papp.
  pose (Qapp := func1 Papp).
  pose (Rapp := func2 Papp).
  pose (RTapp := func3 Qapp).
  pose (Tapp := RTapp Rapp).
  assumption.
Qed.

Lemma weak_peirce : forall P Q, ((((P->Q)->P)->P)->Q)->Q.
Proof.
  intros P Q.
  intros func1.
Qed.





























