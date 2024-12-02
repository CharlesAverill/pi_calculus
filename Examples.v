From Picalc Require Import Interface.

Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation u := "u".
Notation v := "v".

(* Shows that the semantics are non-deterministic

    The state
        x<y>,P | x(u),u<v>,Q | x<z>,R
    can step into two states (ignoring substitution for now):
        (1) P | y<v>,Q | x<y>,R
        (2) x<y>,P | z<v>,Q | R
    
    In (1), the leftmost thread sends the message "y" on the channel "x" to the 
    center thread. The center thread receives, binds its input to "u", and then 
    waits to send on channel "u". After receiving the message from the leftmost
    thread, the sent message "y" is substituted for all occurrences of "u".

    In (2), the same thing happens, but it is instead the rightmost thread that
    sends to the center thread.
*)

Example milner_2_2 : forall P Q R,
    (<{x<y>,P | x(u),u<v>,Q | x<z>,R}> ~>* <{P | y<v>,[u:=y]Q | x<z>,R}>) /\
    (<{x<y>,P | x(u),u<v>,Q | x<z>,R}> ~>* <{x<y>,P | z<v>,[u:=z]Q | R}>).
Proof.
    split.
    - send 0 <-> 1.
    - send 1 <-> 2.
Qed.

Section ChurchNumerals.

    (* A church numeral n in Pi Calculus is a process
       that sends n messages on channel "i" followed 
       by a message on channel "z"
    *)

    (* 
        i - increment 
        z - zero
        q - anonymous value
    *)
    Variable i z q : name.
    Variable i_z_q_diff :
        i <> z /\ i <> q /\ z <> q.

    (* p names are output channels below *)

    Definition zero (p : name) : process :=
        <{z<p>,#}>.

    Definition incr (n : process) (p : name) : process :=
        <{i<p>,n}>.

    (* Read numbers from x and y channels, send sum on p *)
    Definition add (x y p : name) : process :=
        <{!((i(q),p<i>,#) + (z(q),p<z>,#) + #)}>.

    Fixpoint nat_of_proc (p : process) : option nat :=
        match p with
        | <{z<_>,#}> => Some 0
        | <{i<_>,n}> => match nat_of_proc n with
            | Some n' => Some (S n')
            | None => None
            end
        | _ => None
        end.

    Fixpoint proc_of_nat (n : nat) : process :=
        match n with
        | O => zero "p"
        | S n' => incr (proc_of_nat n') "p"
        end.

    Theorem proc_of_Sn :
        forall (n : nat),
        proc_of_nat (S n) = incr (proc_of_nat n) "p".
    Proof. reflexivity. Qed.

    Inductive pnat_wf : process -> Prop :=
    | WfZero : pnat_wf (zero "p")
    | WfIncr : forall p',
        pnat_wf p' ->
        pnat_wf (incr p' "p").

    Theorem proc_of_nat_well_formed :
        forall n, pnat_wf (proc_of_nat n).
    Proof.
        induction n; simpl.
        constructor.
        now constructor.
    Qed.

    Theorem nat_of_incr :
        forall proc,
        pnat_wf proc ->
        nat_of_proc (incr proc "p") = 
            match nat_of_proc proc with
            | Some n => Some (S n)
            | None => None
            end.
    Proof.
        intros. induction proc; simpl; auto.
        inversion H.
    Qed.

    Theorem nat_proc_convert :
        forall (n : nat),
        nat_of_proc (proc_of_nat n) = Some n.
    Proof.
        intros. induction n.
            reflexivity.
        rewrite proc_of_Sn. rewrite nat_of_incr.
        rewrite IHn. reflexivity.
        apply proc_of_nat_well_formed.
    Qed.
End ChurchNumerals.
