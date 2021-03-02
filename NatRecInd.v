(* Definindo a soma *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match m with
    | O => n
    | S m' => S (plus n m')
  end.

(* Exercício x4.5 [Sem recursão] *)
Definition func_d1 (n : nat) : nat :=
  plus n n.

(* Exercício x4.5 [Com recursão] *)
Fixpoint func_d2 (n : nat) : nat :=
  match n with
    | O => O
    | S n' => S (S (func_d2 n'))
  end.

(* Definindo a multiplicação [Exercício x4.6] *)
Fixpoint multi (n : nat) (m : nat) : nat :=
  match m with
    | O => O
    | S m' => plus n (multi n m')
  end.

(* Definindo a exponenciação [Exercício x4.9] *)
Fixpoint expo (n : nat) (m : nat) : nat :=
  match m with
    | O => S m
    | S m' => multi n (expo n m')
  end.

(* Definindo a sequência de Fibonacci [Exercício x4.11] *)
Fixpoint fibo (n : nat) : nat :=
  match n with
  | O => O
  | S O => S O
  | S (S n' as n'') => fibo n'' + fibo n' 
  end.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity).
Notation "x * y" := (multi x y)
                       (at level 40, left associativity).
Notation "x ^ y" := (expo x y)
                       (at level 30, right associativity).

(* Comutatividade da soma *)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    induction m as [| m' IHm'].
    + simpl. reflexivity.
    + simpl. rewrite -> IHm'. simpl. reflexivity.
  - (* n = S n' *)
    induction m as [| m' IHm'].
    + simpl. rewrite <- IHn'. simpl. reflexivity.
    + simpl. rewrite <- IHn'. rewrite -> IHm'. 
      simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Associatividade da soma *)
Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction p as [| p' IHp'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHp'. reflexivity.
Qed.