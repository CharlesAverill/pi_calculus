From Picalc Require Export Processes.

From Coq.Classes Require Export RelationClasses Morphisms.
From Coq.Setoids Require Export Setoid.

Reserved Notation "P '=c=' Q" (at level 40).
Inductive congr : process -> process -> Prop :=
| Congr_refl : forall P, P =c= P
| Congr_sym : forall P Q, P =c= Q -> Q =c= P
| Congr_trans : forall P Q R,
    P =c= Q ->
    Q =c= R ->
    P =c= R
| Congr_Alpha_Equiv : forall x y P,
    ~ In x (free_names P) ->
    P =c= <{[x:=y]P}>
| Congr_Par_Nil : forall P, 
    <{P|#}> =c= <{P}>
| Congr_Par_comm : forall P Q, 
    <{P|Q}> =c= <{Q|P}>
| Congr_Par_assoc : forall P Q R, 
    <{P|Q|R}> =c= <{(P|Q)|R}>
| Congr_Par_inner : forall P P' Q,
    P =c= P' ->
    <{P|Q}> =c= <{P'|Q}>
| Congr_Plus_comm : forall P Q,
    <{P + Q}> =c= <{Q + P}>
| Congr_Plus_assoc : forall P Q R,
    <{P+Q+R}> =c= <{(P+Q)+R}>
| Congr_Plus_inner : forall P P' Q,
    P =c= P' ->
    <{P+Q}> =c= <{P'+Q}>
| Congr_Restrict_Nil : forall x, 
    <{[v x] #}> =c= <{#}>
| Congr_Restrict_comm : forall x y P,
    <{[v x] [v y] P}> =c= <{[v y] [v x] P}>
| Congr_Restrict_Par : forall x P Q,
    ~ In x (free_names P) ->
    <{[v x] (P | Q)}> =c= <{P | ([v x] Q)}>
| Congr_Copy : forall P,
    <{!P}> =c= <{!P | P}>
| Congr_Copy_Nil : <{! #}> =c= <{#}>
| Congr_Copy_Reduce : forall P,
    <{!!P}> =c= <{!P}>
| Congr_Copy_Distr : forall P Q,
    <{!(P|Q)}> =c= <{!P | !Q}>
where "P '=c=' Q" := (congr P Q).

Hint Constructors congr : picalc.

Lemma Congr_Par_rotate_l : forall P Q R,
    <{P|Q|R}> =c= <{Q|R|P}>.
Proof. eauto with picalc. Qed.
    

Lemma Congr_Par_rotate_r : forall P Q R,
    <{P|Q|R}> =c= <{R|P|Q}>.
Proof. eauto with picalc. Qed.

Lemma Congr_Par_swap : forall P Q R,
    <{P|Q|R}> =c= <{Q|P|R}>.
Proof. eauto with picalc. Qed.

Instance congr_eqv_relation : Equivalence congr.
Proof.
  constructor.
    unfold Reflexive. apply Congr_refl.
    unfold Symmetric. apply Congr_sym. 
    unfold Transitive. apply Congr_trans.
Qed.

Add Parametric Relation : process congr
  reflexivity proved by Congr_refl
  symmetry proved by Congr_sym
  transitivity proved by Congr_trans
  as congr_setoid.

Instance par_proper : Proper (eq ==> congr ==> congr) Par.
Proof.
  intros x y Hxy xs ys Hxs. subst.
  eapply Congr_trans, Congr_Par_comm.
  eapply Congr_sym, Congr_trans, Congr_Par_comm.
  now apply Congr_Par_inner, Congr_sym.
Qed.


