Require Export List.
Export ListNotations.
Require Export String.
Open Scope string_scope.

Declare Scope pi_scope.
Create HintDb picalc.

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
    (Plus x y) (in custom picalc at level 99, left associativity) : pi_scope.
Notation "x | y" :=
    (Par x y) (in custom picalc at level 99, left associativity) : pi_scope.
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
