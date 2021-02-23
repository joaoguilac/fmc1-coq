(* Definindo os números naturais *)
Inductive nat : Type :=
  | O
  | S (n : nat).

(* Definindo a soma *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match m with
    | O => n
    | S m' => S (plus n m')
  end.

(* Definindo a multiplicação *)
Fixpoint multi (n : nat) (m : nat) : nat :=
  match m with
    | O => O
    | S m' => plus n (multi n m')
  end.

(* Definindo a exponenciação *)
Fixpoint expo (n : nat) (m : nat) : nat :=
  match m with
    | O => S m
    | S m' => multi n (expo n m')
  end.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (multi x y)
                       (at level 40, left associativity)
                       : nat_scope.
Notation "x ^ y" := (expo x y)
                       (at level 30, right associativity)
                       : nat_scope.

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