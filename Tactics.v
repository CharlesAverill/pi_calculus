From Picalc Require Export Step.

(* Rotate P|Q|R to Q|R|P *)
Tactic Notation "rotate" "left" :=
    match goal with
    | [|- _ =c= _] => apply Congr_Par_rotate_l
    | [|- _ ~> _] => apply Step_Par_rotate_l
    | [|- _ ~>* _] => apply multistep_Par_rotate_l
    end.

(* Rotate P|Q|R to R|P|Q *)
Tactic Notation "rotate" "right" :=
    match goal with
    | [|- _ =c= _] => apply Congr_Par_rotate_r
    | [|- _ ~> _] => apply Step_Par_rotate_r
    | [|- _ ~>* _] => apply multistep_Par_rotate_r
    end.

(* Swap P|Q|R to Q|P|R*)
Ltac parswap :=
    match goal with
    | [|- _ =c= _] => apply Congr_Par_swap
    | [|- _ ~> _] => apply Step_Par_swap
    | [|- _ ~>* _] => apply multistep_Par_swap
    end.

Fixpoint unfold_par (p : process) : list process :=
    match p with
    | <{P|Q}> =>
        P :: unfold_par Q
    | _ => [p]
    end.

Fixpoint fold_par (l : list process) : process :=
    match l with
    | [] => <{#}>
    | [h] => <{h}>
    | h :: t => let T := (fold_par t) in <{h|T}>
    end.

Fixpoint pop {A : Type} (l : list A) (n : nat) : option (A * list A) :=
    match n, l with
    | O, h :: t => Some (h, t)
    | S n', h :: t => 
        match pop t n' with
        | None => None
        | Some (popped, t') =>
            Some (popped, h :: t')
        end
    | _, _ => None
    end.

Definition bring_to_front {A : Type} (l : list A) (x y : nat) : option (list A) :=
    match pop l x with
    | None => None 
    | Some (xitem, l') =>
        match pop l' (y - 1) with
        | None => None
        | Some (yitem, l'') =>
            Some (xitem :: yitem :: l'')
        end
    end.

Definition bring_procs_to_front (p : process) (x y : nat) : process :=
    match bring_to_front (unfold_par p) x y with
    | None => p
    | Some p' =>
        fold_par p'
    end.

Lemma bring_to_front_nil : forall A (l : list A) x y,
    bring_to_front l x y = Some [] ->
    l = [].
Proof.
    induction l; intros. reflexivity.
    unfold bring_to_front in H. destruct (pop (a :: l) x) eqn:E.
    destruct p. destruct (pop l0 (y - 1)) eqn:E0.
    destruct p. inversion H. inversion H. inversion H.
Qed.

Lemma unfold_par_nil : forall p,
    unfold_par p <> [].
Proof.
    induction p; discriminate.
Qed.

Ltac psimpl := 
    cbn [subst String.eqb Ascii.eqb Bool.eqb];
    cbv [bring_procs_to_front bring_to_front unfold_par pop PeanoNat.Nat.sub
        fold_par].
Ltac pauto := psimpl; eauto with picalc.

Ltac step :=
    match goal with
    | [|- ?X ~>* ?Y] => eapply MStep
    end.

(* Backtrack over all IO processes *)
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

(* Solve alpha equivalence congruence goals *)
Ltac mstep_rename_congr xname yname :=
    multimatch goal with
    | [ H0: xname = ?x, H1: yname = ?y |- _ ] =>
        match x with
        | Output ?u1 ?v1 _ => match y with
            | Output ?u2 ?v2 _ =>
                rewrite H0, H1;
                match goal with
                | [|- ?X0 =c= ?Y0] =>
                    change Y0 with <{[u1:=u2](X0)}>
                end;
                now apply Congr_Alpha_Equiv
            end
        end
    end.

(* Solve alpha equivalence multistep goals *)
Ltac mstep_rename :=
    multimatch goal with
    | [|- <{?X}> ~>* <{?Y}>] =>
        normalize_par;
        let xname := fresh "term" in
        let yname := fresh "term" in
        get_in_out_procs X xname;
        get_in_out_procs Y yname;
        eapply MCongr;
        mstep_rename_congr xname yname
    end.

Tactic Notation "bring" "to" "front" constr(x) constr(y) :=
    match goal with [|- ?X ~> ?Y] =>
        eapply SStruct with (P := bring_procs_to_front X x y);
            [pauto|psimpl|reflexivity]
    end.

Tactic Notation "send" constr(x) "->" constr(y) :=
    bring to front x y;
    match goal with
    | [|- <{_(_),_|_<_>,_|_}> ~> _] =>
        parswap
    | [|- <{_(_),_|_<_>,_}> ~> _] =>
        parswap
    | _ => idtac
    end;
    eapply SStruct;
        [apply Congr_Par_assoc
        |apply SPar, SInput
        |idtac].
