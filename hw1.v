(*1. Proposições de dupla negação*)
Theorem doubleneg_intro : forall (p : Prop), p -> ~ ~ p.
Proof.
  intros p. (**Declaro uma variável do tipo proposição para ser meu
           "parâmetro"*)
  intro H. (**Aqui eu to tipo fazendo um "suponha", atacando
          meu alvo*)
  unfold not. (*Aqui abro a definição do meu alvo (pois possui negações)**)
  intros A1. (*Rotulo um valor para ser o meu ¬p, pois estamos fazendo
            ¬p => false**)
  apply (A1 H). (*Vamos aplicar o que foi definido no meu teorema**)
Qed.

Definition Lem : Prop := forall (p : Prop), p \/ ~p.

Theorem doubleneg_elim : Lem -> forall (p : Prop), ~~ p -> p.
Proof.
  unfold not.
  intros lem p Hnnp.
  destruct (lem p) as [Hp | Hnp].
   - apply Hp.
   - unfold not in Hnp. apply Hnnp in Hnp as Hbot. contradiction.
Qed.


(*2. A irrefutabilidade do LEM*)
Theorem irr_Lem : Lem -> forall (p : Prop), ~~(p \/ ~p).
Proof.
  intro Hlem.
  intro p.
  intros Hn_ou.
  unfold not in Hn_ou.
  apply Hn_ou in Hlem.
  apply Hlem.
Qed.


(*3. A lei de Peirce e sua versão “fraca”*)
Theorem Peirce_1 : Lem -> forall (p q : Prop), ((p -> q) -> p) -> p.
Proof.
  intro Hlem.
  intros p q H.
  destruct (Hlem p) as [Hp | Hnp].
  - apply Hp.
  - assert (H_im : p -> q).
    + intro Hp. contradiction.
    + apply H in H_im as Hp.
      apply Hp.
Qed.

Theorem Peirce_2 : forall (p q : Prop), ((p -> q) -> p) -> ~~p.
Proof.
  intros p q H.
  intro Hnp.
  assert (H_im : p -> q).
    { intro Hp. contradiction. }
  apply H in H_im as Hp.
  apply Hnp in Hp as Hbot.
  apply Hbot.
Qed.


(*4. Proposições de interdefinabilidade dos =>,V*)
Theorem inter_im_dis_1 : Lem -> forall (p q : Prop), (p -> q) -> (~p \/ q).
Proof.
  intros Hlem p q H.
  destruct (Hlem p) as [Hp | Hnp].
  - right. apply H in Hp as Hq. apply Hq.
  - left. apply Hnp.
Qed.

Theorem inter_im_dis_2 : forall (p q : Prop), (~p \/ q) -> (p -> q).
Proof.
  intros p q H.
  intro Hp.
  destruct H as [Hnp | Hq].
  - contradiction.
  - apply Hq. 
Qed.

Theorem inter_im_dis_3 : forall (p q : Prop), (p \/ q) -> (~p -> q).
Proof.
  intros p q H.
  intro Hnp.
  destruct H as [Hp | Hq].
  - contradiction.
  - apply Hq. 
Qed.

Theorem inter_im_dis_4 : Lem -> forall (p q : Prop), (~p -> q) -> (p \/ q).
Proof.
  intros Hlem p q H.
  destruct (Hlem p) as [Hp | Hnp].
  - left. apply Hp.
  - right. apply H in Hnp as Hq. apply Hq.  
Qed.


(*5. Proposições de interdefinabilidade dos \/,/\*)
Theorem inter_dis_con_1 : forall (p q : Prop), (p \/ q) -> ~(~p /\ ~q).
Proof.
  intros p q H.
  intro Hdis.
  destruct H as [Hp | Hq].
    { destruct Hdis as [Hnp Hnq]. contradiction. }
    { destruct Hdis as [Hnp Hnq]. contradiction. }
Qed.

Theorem inter_dis_con_2 : Lem -> forall (p q : Prop), ~(~p /\ ~q) -> (p \/ q).
Proof.
  intros Hlem p q H.
  destruct (Hlem p) as [Hp | Hnp].
  - destruct (Hlem q) as [Hq | Hnq].
    + left. apply Hp.
    + left. apply Hp.
  - destruct (Hlem q) as [Hq | Hnq].
    + right. apply Hq.
    + assert (H_con : ~p /\ ~q).
        { split. apply Hnp. apply Hnq. }
      apply H in H_con as Hbot. contradiction.
Qed.

Theorem inter_dis_con_3 : forall (p q : Prop), p /\ q -> ~(~p \/ ~q).
Proof.
  intros p q H.
  destruct H as [Hp Hq].
  unfold not.
  intro H_dis.
  destruct H_dis as [Hnp | Hnq].
   { apply Hnp in Hp as Hbot. apply Hbot. }
   { apply Hnq in Hq as Hbot. apply Hbot. }
Qed.

Theorem inter_dis_con_4 : Lem -> forall (p q : Prop), ~(~p \/ ~q) -> p /\ q.
Proof.
  intros Hlem p q H.
  unfold not in H.
  destruct (Hlem p) as [Hp | Hnp].
  - destruct (Hlem q) as [Hq | Hnq].
    + split. apply Hp. apply Hq.
    + assert (H_dis : ~p \/ ~q).
      { right. apply Hnq. }
      apply H in H_dis as Hbot. contradiction.
  - assert (H_dis : ~p \/ ~q).
      { left. apply Hnp. }
      apply H in H_dis as Hbot. contradiction.
Qed.

(*6. As leis de De Morgan*)
Theorem DeMorgan_1 : Lem -> forall (p q : Prop), ~(p \/ q) -> (~p /\ ~q).
Proof.
  intros Hlem p q H.
  unfold not in H.
  destruct (Hlem p) as [Hp | Hnp].
<<<<<<< HEAD
=======
  
>>>>>>> 37c389d355ddceddf3d9fe1177fb9ea5d2b06ca3
Qed. 

As leis de De Morgan:
¬(P \/ Q) => (¬P /\ ¬Q)
¬(P \/ Q) <= (¬P /\ ¬Q)
¬(P /\ Q) => (¬Q \/ ¬P)
¬(P /\ Q) <= (¬Q \/ ¬P)