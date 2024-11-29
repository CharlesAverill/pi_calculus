Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Declare Scope pi_scope.

Definition name : Set := string.

Inductive process : Set :=
| Input     (x : name) (y : name) (P : process)
| Output    (x : name) (y : name) (P : process)
| Par       (P Q : process)
| Plus      (P Q : process)
| Restrict  (x : name) (P : process)
| Copy      (P : process)
| Nil.

Declare Custom Entry picalc.
Notation "<{ e }>" := e (e custom picalc at level 99) : pi_scope.
Notation "( x )" := x (in custom picalc, x at level 99) : pi_scope.
Notation "x" := x 
    (in custom picalc at level 0, x constr at level 0) : pi_scope.
Notation "x ( y ) , P" := 
    (Input x y P) (in custom picalc at level 90,
        (* x at level 91, *)
        y at level 91,
        P at level 91) : pi_scope.
Notation "x < y > , P" :=
    (Output x y P) (in custom picalc at level 90,
        (* x at level 91, *)
        y at level 91,
        P at level 91) : pi_scope.
Notation "x + y" :=
    (Plus x y) (in custom picalc at level 99, right associativity) : pi_scope.
Notation "x | y" :=
    (Par x y) (in custom picalc at level 99, right associativity) : pi_scope.
Notation "[ 'v' x ] P" :=
    (Restrict x P) (in custom picalc at level 90,
        x at level 91,
        right associativity) : pi_scope.
Notation "! P" := 
    (Copy P) (in custom picalc at level 90,
        P at level 91) : pi_scope.
Notation "#" := 
    Nil (in custom picalc at level 0) : pi_scope.
Open Scope pi_scope.

(* Inductive free_names : process -> list name -> Prop :=
| FN_Input : forall x y P l,
    free_names P l ->
    free_names <{ x (y), P }> (remove string_dec y l)
| FN_Output : forall x y P l,
    free_names P l ->
    free_names <{ x <y>, P }> l
| FN_Par : forall P l1 Q l2,
    free_names P l1 ->
    free_names Q l2 ->
    free_names <{ P | Q }> (l1 ++ l2)
| FN_Restrict : forall x P l,
    free_names P l ->
    free_names <{ [ v x ] P }> l
| FN_Copy : forall P l,
    free_names P l ->
    free_names <{ ! P }> l
| FN_Nil : free_names <{ # }> []. *)

Fixpoint free_names (p : process) : list name :=
    match p with
    | <{x(y),P}> => remove string_dec y (free_names P)
    | <{x<y>,P}> => free_names P
    | <{P|Q}> | <{P+Q}> => free_names P ++ free_names Q
    | <{[v x] P}> => free_names P
    | <{!P}> => free_names P
    | <{#}> => []
    end.

Reserved Notation "'[' x ':=' s ']' t" (in custom picalc at level 20, x constr).
Fixpoint subst (x : name) (s : name) (t : process) : process :=
  match t with
  | <{y(z),P}> =>
      if x =? y then
        <{s(z),[x:=s]P}>
      else 
        <{y(z),[x:=s]P}>
  | <{y<z>,P}> =>
      (* If x is the same as x (the output name), don't substitute inside, else substitute *)
      if x =? y then 
        <{s<z>,[x:=s]P}>
      else 
        <{y<z>,[x := s]P}>
  | <{P|Q}> =>
      <{([x := s] P)|([x := s] Q)}>
  | <{P+Q}> =>
      <{([x := s] P) + ([x := s] Q)}>
  | <{[v y]P}> =>
    if x =? y then
        t
    else
        <{[v y] ([x := s] P)}>
  | <{!P}> =>
      <{! ([x := s] P)}>
  | <{#}> => <{#}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom picalc).

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

Create HintDb picalc.
Hint Constructors congr : picalc.

Reserved Notation "P '~>' Q" (at level 40).
Inductive step : process -> process -> Prop :=
| SInput : forall x y z P Q,
    <{(x<z>,P)|(x(y),Q)}> ~> <{P|([z := y]Q)}>
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

Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation u := "u".
Notation v := "v".
Notation w := "w".

Lemma Congr_Par_rotate : forall P Q R,
    <{P|Q|R}> =c= <{Q|R|P}>.
Proof. eauto with picalc. Qed.

(* Shows that the semantics are non-deterministic

    The state
        x<y>,# | x(u),u<v>,# | x<y>,#
    can step into two states:
        (1) # | y<v>,# | x<y>,#
        (2) x<y>,# | z<v>,# | #
    
    In (1), the leftmost thread sends the message "y" on the channel "x" to the 
    center thread. The center thread receives, binds its input to "u", and then 
    waits to send on channel "u". After receiving the message from the leftmost
    thread, the sent message "y" is substituted for all occurrences of "u".

    In (2), the same thing happens, but it is instead the rightmost thread that
    sends to the center thread.
*)
Example milner_2_2 :
    (<{x<y>,# | x(u),u<v>,# | x<y>,#}> ~>* <{# | y<v>,# | x<y>,#}>) /\
    (<{x<y>,# | x(u),u<v>,# | x<y>,#}> ~>* <{x<y>,# | z<v>,# | #}>).
Proof.
    split.
    - eapply MStep.
        -- eapply SStruct.
            + eapply Congr_Par_assoc.
            + apply SPar. apply SInput.
            + cbn [subst String.eqb Ascii.eqb Bool.eqb].
                apply Congr_refl.
        -- apply MCongr. eapply Congr_trans.
            apply Congr_sym, Congr_Par_assoc.
            change <{ # | "y" < "v" > , # | "x" <"y">, # }> with
                (<{["u":="y"] (# | "u" < "v" > , # | "x" <"y">, #) }>).
            now apply Congr_Alpha_Equiv.
    - eapply MStep.
        -- eapply SStruct with 
            (P := <{ (x<y>,# | x(u),u<v>,#) | x<y>,# }>).
            + eauto with picalc.
            + apply SPar. apply SInput.
            + cbn [subst String.eqb Ascii.eqb Bool.eqb].
                apply Congr_refl.
        -- apply MCongr. apply Congr_trans with (Q := <{x<y>,# | u<v>,# | #}>).
            eauto with picalc.
            change <{x<y>,#|z<v>,#|#}> with <{[u:=z](x<y>,#|u<v>,#|#)}>.
            now apply Congr_Alpha_Equiv.
Qed.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Instance bag_eqv_relation : Equivalence congr.
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

Add Parametric Relation : process multistep
  transitivity proved by MTrans
  as multistep_setoid.

Instance par_proper : Proper (eq ==> congr ==> congr) Par.
Proof.
  intros x y Hxy xs ys Hxs. subst.
  eapply Congr_trans, Congr_Par_comm.
  eapply Congr_sym, Congr_trans, Congr_Par_comm.
  now apply Congr_Par_inner, Congr_sym.
Qed.

Instance multistep_proper : 
    forall P, Proper (congr ==> Basics.flip Basics.impl) (multistep P).
Proof.
    intros P x y Hxy. unfold Basics.flip, Basics.impl. intro.
    eapply MTrans. apply H. apply MCongr, Congr_sym, Hxy.
Qed.

Instance multistep_proper' : 
    forall P, Proper (congr ==> Basics.impl) (multistep P).
Proof.
    intros P x y Hxy. unfold Basics.impl. intro.
    eapply MTrans. apply H. apply MCongr, Hxy.
Qed.

Ltac psimpl := cbn [subst String.eqb Ascii.eqb Bool.eqb].
Ltac pauto := psimpl; eauto with picalc.

Ltac step :=
    match goal with
    | [|- ?X ~>* ?Y] => eapply MStep
    end.

Ltac get_in_out_procs p name :=
    multimatch p with
    | <{_<_>,_}> => remember p as name
    | <{_(_),_}> => remember p as name
    | <{?P|?Q}> => get_in_out_procs P name + get_in_out_procs Q name
    end.

Ltac normalize_par :=
    repeat match goal with
    | [|- context[<{?A|?B|?C}>]] =>
        rewrite Congr_Par_assoc
    end.

Ltac mstep_rename :=
    multimatch goal with
    | [|-context[<{?X}> ~>* <{?Y}>]] =>
        normalize_par;
        let xname := fresh "term" in
        let yname := fresh "term" in
        get_in_out_procs X xname;
        get_in_out_procs Y yname;
        eapply MCongr;
        idtac xname yname;
        multimatch goal with
        | [ H0: xname = ?x, H1: yname = ?y |- _ ] =>
            match x with
            | Output ?u1 ?v1 _ => match y with
                | Output ?u2 ?v2 _ =>
                    idtac H0 H1;
                    rewrite H0, H1;
                    match goal with
                    | [|- ?X0 =c= ?Y0] =>
                        change Y0 with <{[u1:=u2](X0)}>
                    end;
                    now apply Congr_Alpha_Equiv
                end
            end
        end
    end.

Example milner_2_2' :
    (<{x<y>,# | x(u),u<v>,# | x<y>,#}> ~>* <{# | y<v>,# | x<y>,#}>) /\
    (<{x<y>,# | x(u),u<v>,# | x<y>,#}> ~>* <{x<y>,# | z<v>,# | #}>).
Proof with pauto.
    split.
    - step.
        -- eapply SStruct.
            + pauto.
            + pauto.
            + psimpl. reflexivity.
        -- mstep_rename.
    - step.
        -- eapply SStruct with 
            (P := <{ (x<y>,# | x(u),u<v>,#) | x<y>,# }>)...
        -- transitivity <{x<y>,# | u<v>,# | #}>... mstep_rename.
Qed.
