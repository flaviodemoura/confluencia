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
  
Qed.