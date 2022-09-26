From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Lia.

Fixpoint max2 (n m : nat) :=
  match n, m with
  | S n', S m' => S (max2 n' m')
  | 0, _ => m
  | _, 0 => n
  end.

Example max2_test1 : max2 3 4 = 4.
Proof.
  simpl.
  reflexivity.
Qed.

Example max2_test2 : max2 5 0 = 5.
Proof.
  simpl.
  reflexivity.
Qed.

Example max2_test3 : max2 0 0 = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Example max2_test4 : max2 4 4 = 4.
Proof.
  simpl.
  reflexivity.
Qed.

Fixpoint maxn (l : list nat) : nat :=
  match l with
  | nil => 0
  | h::t => max2 h (maxn t)
  end.

Fixpoint gcra1_rec (l : list nat) (T tau LCT X1 : nat) : bool :=
  match l with
  | nil => true
  | h::tail =>
      let t := LCT + h in
      if ((t + tau) <? X1)
      then false
      else gcra1_rec tail T tau t ((max2 t X1) + T)
  end.

Definition gcra1 (l : list nat) (T tau : nat) : bool :=
  gcra1_rec l T tau 0 0.

Definition conformant := [0; 10; 8; 10; 10; 10].
Definition nonconformant := [0; 10; 8; 10; 10; 10; 9].

Example gcra1_test1 : gcra1 conformant 10 2 = true.
Proof.
  unfold gcra1.
  simpl.
  reflexivity.
Qed.

Example gcra1_test2 : gcra1 nonconformant 10 2 = false.
Proof.
  unfold gcra1.
  simpl.
  reflexivity.
Qed.

Fixpoint gcra2_rec (l : list nat) (T tau LCT X2 : nat) : bool :=
  match l with
  | nil => true
  | h::tail =>
      let t := LCT + h in
      if (tau <? (X2 + LCT - t))
      then false
      else gcra2_rec tail T tau t ((X2 + LCT - t) + T)
  end.


Definition gcra2 (l : list nat) (T tau : nat) : bool :=
  gcra2_rec l T tau 0 0.


Example gcra2_test1 : gcra2 conformant 10 2 = true.
Proof.
  unfold gcra2.
  simpl.
  reflexivity.
Qed.

Example gcra2_test2 : gcra2 nonconformant 10 2 = false.
Proof.
  unfold gcra2.
  simpl.
  reflexivity.
Qed.

Locate "<?".
Print Nat.ltb.
Locate "<=?".
Print Nat.leb.
Search Nat.leb.
Search (_ + _ + _).


Lemma lt_elim : forall x y z, (x + y <? x + z) = (y <? z).
Proof.
Admitted.

Lemma minus_plus : forall x y z, x - (y + z) = x - y - z.
Proof.
Admitted.

Lemma minus_self_comm : forall x y, x + y - x = y.
Proof.
Admitted.

Lemma lt_shift : forall x y z, (x + y <? z) = (x <? z - y).
Proof.
Admitted.

Lemma max_plus : forall x y z, max2 (x + y) (x + z) = max2 y z + x.
Proof.
Admitted.

Lemma minus_self_comm' : forall x y z, x + y - (x + z) = y - z.
Proof.
Admitted.

Lemma max_0 : forall x y, x - y = max2 (x - y) 0.
Proof.
Admitted.

Lemma max2_symm : forall x y, max2 x y = max2 y x.
Proof.
Admitted.

Lemma max2_extract : forall x y, max2 x y = max2 (x - y) 0 + y.
Proof.
Admitted.

Lemma add_rearrange : forall a b c d, a + b + c + d = a + d + c + b.
Proof.
Admitted.

Lemma add_order : forall a b c d, a + b + c + d = a + b + (c + d).
Proof.
Admitted.

Lemma convert_gcra_rec : forall l, forall T tau LCT X2,
    gcra1_rec l T tau LCT (X2 + LCT) =
      gcra2_rec l T tau LCT X2.
Proof.
  induction l as [|h t].
  - (* l = [] *)
    intros.
    simpl.
    reflexivity.
  - (* l = h :: t *)
    intros.
    assert (fail_eq: (tau <? X2 + LCT - (LCT + h)) = (LCT + h + tau <? X2 + LCT)).
    -- (* prove fail_eq *)
      rewrite Nat.add_comm with (n := X2) (m := LCT).
      rewrite <- Nat.add_assoc with (n := LCT) (m := h) (p := tau).
      rewrite lt_elim with (x := LCT) (y := (h + tau)) (z := X2).
      rewrite minus_plus with (x := (LCT + X2)) (y := LCT) (z := h).
      rewrite minus_self_comm with (x := LCT) (y := X2).
      symmetry.
      rewrite Nat.add_comm.
      apply lt_shift.
    -- (* use fail_eq *)      
      case (tau <? X2 + LCT - (LCT + h)) eqn:h_nonconformant.
      --- (* h_nonconformant = true *)
        unfold gcra1_rec.
        rewrite <- fail_eq.
        unfold gcra2_rec.
        rewrite h_nonconformant.
        reflexivity.
      --- (* h_nonconformant = false *)
        unfold gcra1_rec.
        rewrite <- fail_eq.
        unfold gcra2_rec.
        rewrite h_nonconformant.
        rewrite Nat.add_comm with (n := X2) (m := LCT).
        rewrite max_plus.
        rewrite minus_self_comm'.
        rewrite max_0 with (x := X2) (y := h).
        rewrite max2_symm with (x := h) (y := X2).
        rewrite max2_extract with (x := X2) (y := h).
        rewrite add_rearrange with (a := max2 (X2 - h) 0) (b := h) (c := LCT) (d := T).
        unfold gcra1_rec in IHt.
        unfold gcra2_rec in IHt.
        rewrite add_order with (a := max2 (X2 - h) 0) (b := T) (c := LCT) (d := h).
        apply IHt with (T := T) (tau := tau) (X2 := max2 (X2 - h) 0 + T) (LCT := LCT + h).
Qed.

Theorem gcra1_eq_gcra2 : forall l, forall T tau,
    gcra1 l T tau = gcra2 l T tau.
Proof.
  intros.
  unfold gcra1.
  unfold gcra2.  
  rewrite convert_gcra_rec with (X2 := 0) (LCT := 0).
  reflexivity.
Qed.
