From Picalc Require Export Congruence.

Reserved Notation "P '~>' Q" (at level 40).
Inductive step : process -> process -> Prop :=
| SInput : forall x y z P Q,
    <{(x<z>,P)|(x(y),Q)}> ~> <{P|([y := z]Q)}>
| SPar : forall P P' Q,
    P ~> P' ->
    <{P|Q}> ~> <{P'|Q}>
| SPlus : forall P P' Q,
    P ~> P' ->
    <{P+Q}> ~> P'
| SRes : forall P P' x,
    P ~> P' ->
    <{[v x]P}> ~> <{[v x]P'}>
| SStruct : forall P P' Q Q',
    Q =c= P ->
    P ~> P' ->
    P' =c= Q' ->
    Q ~> Q'
where "P '~>' Q" := (step P Q).

Hint Constructors step : picalc.

Reserved Notation "P ~>* Q" (at level 40).
Inductive multistep : process -> process -> Prop :=
| MCongr : forall P Q,
    P =c= Q ->
    P ~>* Q
| MStep : forall P Q R,
    P ~> Q ->
    Q ~>* R ->
    P ~>* R
| MTrans : forall P Q R,
    P ~>* Q ->
    Q ~>* R ->
    P ~>* R
where "P ~>* Q" := (multistep P Q).

Hint Constructors multistep : picalc.

Lemma MRefl : forall P, P ~>* P.
Proof.
    intros. apply MCongr. apply Congr_refl.
Qed.
Hint Resolve MRefl : picalc.

Lemma Step_Par_rotate_l : forall P Q R X,
    <{Q|R|P}> ~> X ->
    <{P|Q|R}> ~> X.
Proof. eauto with picalc. Qed.

Lemma Step_Par_rotate_r : forall P Q R X,
    <{R|P|Q}> ~> X ->
    <{P|Q|R}> ~> X.
Proof. eauto with picalc. Qed.

Lemma Step_Par_swap : forall P Q R X,
    <{Q|P|R}> ~> X ->
    <{P|Q|R}> ~> X.
Proof. eauto with picalc. Qed.

Lemma multistep_Par_rotate_l : forall P Q R X,
    <{Q|R|P}> ~>* X ->
    <{P|Q|R}> ~>* X.
Proof. eauto with picalc. Qed.

Lemma multistep_Par_rotate_r : forall P Q R X,
    <{R|P|Q}> ~>* X ->
    <{P|Q|R}> ~>* X.
Proof. eauto with picalc. Qed.

Lemma multistep_Par_swap : forall P Q R X,
    <{Q|P|R}> ~>* X ->
    <{P|Q|R}> ~>* X.
Proof. eauto with picalc. Qed.

Lemma mstep_congr_trans :
    forall P Q R,
    P =c= Q ->
    Q ~>* R ->
    P ~>* R.
Proof.
    eauto with picalc.
Qed.

Add Parametric Relation : process multistep
  transitivity proved by MTrans
  as multistep_setoid.

Instance multistep_proper : 
    forall P, Proper (congr ==> Basics.impl) (multistep P).
Proof.
    intros P x y Hxy. unfold Basics.impl. intro.
    eapply MTrans. apply H. apply MCongr, Hxy.
Qed.
