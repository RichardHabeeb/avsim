Require Import QArith.

(** ##############################################################################
QARITH LEMMAS 
################################################################################*)

Lemma Qplus_neg: forall a b, a - b == a + (-b).
Proof.
  intros.
  ring.
Qed.

Lemma Qplus_opp_l : forall q, -q + q == 0.
Proof. intros; ring. Qed.


Lemma Qdiv_mult_inv: forall a b, a / b == a * /b.
Proof.
  intros.
  auto with qarith.
Qed.

Lemma Qmult_neg_1: forall a, a * -(1) == -a.
Proof.
  intros.
  ring.
Qed.

Lemma Qmult_inv_l: forall a, ~ a == 0 -> /a * a == 1.
Proof.
  intros.
  rewrite Qmult_comm.
  rewrite Qmult_inv_r; auto with qarith.
Qed.

Lemma Qplus_double: forall a, a + a == (2 # 1)*a.
Proof.
  intros.
  ring.
Qed.

Lemma Qplus_half: forall a, a/(2#1) + a/(2#1) == a.
Proof.
  intros.
  rewrite Qplus_double.
  rewrite Qmult_div_r; [|unfold Qeq]; auto with qarith.
Qed.

Lemma Qneg_0: - 0 == 0.
Proof.
  ring.
Qed.

Lemma Qeq_neg : forall a b, - a == b <-> a == -b.
Proof.
  intros.
  split; intros; 
    rewrite <- Qmult_neg_1;
    apply Qmult_inj_r with (z:=-(1)); auto with qarith;
    rewrite !Qmult_neg_1, Qopp_opp; trivial.
Qed.

Lemma Qdiv_neg_l: forall a b, (-a)/b == -(a/b).
Proof.
  intros.
  rewrite Qdiv_mult_inv.
  rewrite <- Qmult_neg_1.
  rewrite <- Qmult_assoc.
  rewrite Qmult_comm.
  rewrite <- Qmult_assoc.
  rewrite Qmult_comm.
  rewrite Qmult_neg_1.
  rewrite Qmult_comm.
  rewrite Qdiv_mult_inv.
  reflexivity.
Qed.

Lemma Qmult_neg_l: forall a b, (-a)*b == -(a*b).
Proof.
  intros *.
  rewrite <- Qmult_neg_1, Qmult_comm, Qmult_assoc, Qmult_neg_1, Qmult_comm.
  reflexivity.
Qed.

Lemma Qopp_lt_compat : forall p q, p<q -> -q < -p.
Proof.
  intros (a1,a2) (b1,b2); unfold Qlt; simpl.
  rewrite !Z.mul_opp_l. omega.
Qed.

Lemma Qlt_0_neg_lt_not_r: forall a, 0 < -a -> ~ 0 < a.
Proof.
  intros.
  intuition.
  apply Qopp_lt_compat in H0.
  rewrite Qneg_0 in H0.
  apply Qlt_trans with (x:=0) (y:=-a) (z:=0) in H; trivial.
  apply Qlt_irrefl in H as G.
  contradiction.
Qed.

Lemma Qlt_0_pos_lt_not_l: forall a, a < 0 -> ~ -a < 0.
Proof.
  intros.
  intuition.
  apply Qopp_lt_compat in H0.
  rewrite Qneg_0 in H0.
  rewrite Qopp_opp in H0.
  apply Qlt_trans with (x:=0) (y:=a) (z:=0) in H; trivial.
  apply Qlt_irrefl in H as G.
  contradiction.
Qed.

Lemma Qlt_0_neg_lt_not_l: forall a, -a < 0 -> ~ a < 0.
Proof.
  intros.
  intuition.
  apply Qopp_lt_compat in H0.
  rewrite Qneg_0 in H0.
  apply Qlt_trans with (x:=0) (y:=-a) (z:=0) in H; trivial.
  apply Qlt_irrefl in H as G.
  contradiction.
Qed.

Lemma Qlt_not_lt: forall a b, a < b -> ~ b < a.
Proof.
  intros.
  auto with qarith.
Qed.


Lemma Qmult_lt_0 : forall a b, b > 0 -> a * b < 0 <-> a < 0.
Proof.
  intros * Hb.
  split; intros H.
  {
    apply Qmult_lt_r with (z:=/b) in H.
    - rewrite <- !Qdiv_mult_inv, Qdiv_mult_l in H; auto with qarith.
      rewrite Qdiv_mult_inv, Qmult_0_l in H; trivial.
    - apply Qinv_lt_0_compat; trivial.
  }
  apply Qmult_lt_r with (z:=/b).
  - apply Qinv_lt_0_compat; trivial.
  - rewrite <- !Qdiv_mult_inv, Qdiv_mult_l; auto with qarith.
    rewrite Qdiv_mult_inv, Qmult_0_l; trivial.
Qed.

Lemma Qmult_0_lt : forall a b, b > 0 -> a * b > 0 <-> a > 0.
Proof.
  intros * Hb.
  split; intros H.
  {
    apply Qmult_lt_r with (z:=/b) in H.
    - rewrite <- !Qdiv_mult_inv, Qdiv_mult_l in H; auto with qarith.
      rewrite Qdiv_mult_inv, Qmult_0_l in H; trivial.
    - apply Qinv_lt_0_compat; trivial.
  }
  apply Qmult_lt_r with (z:=/b).
  - apply Qinv_lt_0_compat; trivial.
  - rewrite <- !Qdiv_mult_inv, Qdiv_mult_l; auto with qarith.
    rewrite Qdiv_mult_inv, Qmult_0_l; trivial.
Qed.

Lemma Qmult_eq_0_l : forall a b, b > 0 -> a * b == 0 <-> a == 0.
Proof.
  intros * Hb.
  split; intros H.
  {
    apply Qmult_inj_r with (z:=b); auto with qarith.
    rewrite Qmult_0_l; trivial.
  }
  apply Qmult_inj_r with (z:=b) in H; auto with qarith.
  rewrite Qmult_0_l in H; trivial.
Qed.


Lemma Qeq_by_elim : forall a, ~ a < 0 -> ~ 0 < a -> a == 0.
Proof.
  intros.
  destruct (Q_dec (a) 0) as [[? | ?] | ?]; try contradiction.
  trivial.
Qed.

Lemma Qeq_0_by_eq_neg : forall a b, - a == b -> a == b -> a == 0.
Proof.
  intros * Hn He.
  rewrite He in Hn.
  destruct (Q_dec (b) 0) as [[C | C] | C].
  - apply Qlt_not_lt in C as C0.
    rewrite <- Hn in C.
    apply Qlt_0_neg_lt_not_l in C.
    apply Qeq_by_elim in C; trivial.
    rewrite <- He in C; trivial.
  - apply Qlt_not_lt in C as C0.
    rewrite <- Hn in C.
    apply Qlt_0_neg_lt_not_r in C.
    apply Qeq_by_elim in C; trivial.
    rewrite <- He in C; trivial.
  - rewrite <- He in C; trivial.
Qed.

Lemma Qplus_l_equ_sub_r: forall a b c, a + b == c <-> a == c - b.
Proof.
  intros.
  split; intros H.
  - rewrite <- Qplus_inj_r with (x:=a) (y:=c-b) (z:=b).
    rewrite Qplus_neg.
    rewrite <- Qplus_assoc with (x:=c) (y:=-b) (z:= b).
    rewrite Qplus_opp_l.
    rewrite Qplus_0_r.
    exact H.
  - rewrite <- Qplus_inj_r with (x:=a+b) (y:=c) (z:=-b).
    rewrite <- Qplus_assoc with (x:=a) (y:=b) (z:=-b).
    rewrite Qplus_opp_r.
    rewrite Qplus_0_r.
    rewrite <- Qplus_neg.
    exact H.
Qed.

Lemma Qplus_l_equ_sub_l: forall a b c, a + b == c <-> b == c - a.
Proof.
  intros.
  split; intros H.
  - apply Qplus_l_equ_sub_r.
    rewrite Qplus_comm.
    exact H.
  - apply Qplus_l_equ_sub_r in H.
    rewrite Qplus_comm in H.
    exact H.
Qed.

Lemma Qplus_r_equ_sub_r: forall a b c, c == a + b <-> c - b == a.
Proof.
  intros.
  split; intros H; apply Qeq_sym; apply Qeq_sym in H; apply Qplus_l_equ_sub_r; exact H.
Qed.

Lemma Qplus_r_equ_sub_l: forall a b c, c == a + b <-> c - a == b.
Proof.
  intros.
  split; intros H; apply Qeq_sym; apply Qeq_sym in H; apply Qplus_l_equ_sub_l; exact H.
Qed.


Lemma Qplus_l_lt_sub_r: forall a b c, a + b < c <-> a < c - b.
Proof.
  intros.
  split; intros H.
  - apply Qplus_lt_le_compat with (z:=-b) (t:=-b) in H; auto with qarith.
    rewrite <- Qplus_assoc in H.
    rewrite Qplus_opp_r in H.
    rewrite Qplus_0_r in H.
    rewrite Qplus_neg.
    assumption.
  - apply Qplus_lt_le_compat with (z:=b) (t:=b) in H; auto with qarith.
    rewrite Qplus_neg in H.
    rewrite <- Qplus_assoc in H.
    rewrite Qplus_opp_l in H.
    rewrite Qplus_0_r in H.
    assumption.
Qed.

Lemma Qplus_l_lt_sub_l: forall a b c, a + b < c <-> b < c - a.
Proof.
  intros.
  split; intros H.
  - apply Qplus_l_lt_sub_r.
    rewrite Qplus_comm.
    exact H.
  - apply Qplus_l_lt_sub_r in H.
    rewrite Qplus_comm in H.
    exact H.
Qed.


Lemma Qlt_r_sub_le_weak_l : forall a a' b c, c < a - b -> a <= a' -> c < a' - b.
Proof.
  intros * H H0.
  apply Qplus_le_compat with (z:=-b) (t:=-b) in H0; auto with qarith.
  rewrite <- !Qplus_neg in H0.
  apply Qlt_le_trans with (y:=a - b); trivial.
Qed.

Lemma Qlt_l_plus_le_weak_l: forall a a' b c, a + b < c -> a' <= a -> a' + b < c.
Proof.
  intros * H H0.
  apply Qplus_le_compat with (z:=b) (t:=b) in H0; auto with qarith.
  apply Qle_lt_trans with (z:=c) in H0; trivial.
Qed.

Lemma Qlt_l_plus_le_weak_r: forall a b b' c, a + b < c -> b' <= b -> a + b' < c.
Proof.
  intros * H H0.
  rewrite Qplus_comm.
  apply Qlt_l_plus_le_weak_l with (a:=b); trivial.
  rewrite Qplus_comm; trivial.
Qed.


Lemma Qlt_r_plus_le_weak_l: forall a a' b c, c < a + b -> a <= a' -> c < a' + b.
Proof.
  intros * H H0.
  apply Qplus_le_compat with (z:=b) (t:=b) in H0; auto with qarith.
  apply Qlt_le_trans with (z:=a'+b) in H; trivial.
Qed.

Lemma Qlt_r_plus_le_weak_r: forall a b b' c, c < a + b -> b <= b' -> c < a + b'.
Proof.
  intros * H H0.
  rewrite Qplus_comm.
  apply Qlt_r_plus_le_weak_l with (a:=b); [rewrite Qplus_comm|]; trivial.
Qed.


Lemma Qplus_neg_half_l: forall a, -a + a/(2#1) == -(a/(2#1)).
Proof.
  intros.
  rewrite Qplus_l_equ_sub_r.
  rewrite Qplus_neg.
  apply Qeq_sym.
  rewrite <- Qdiv_neg_l.
  rewrite Qplus_half.
  reflexivity.
Qed.


Lemma Qmult_l_equ_div_r: forall a b c, ~ b == 0 -> a * b == c <-> a == c/b.
Proof.
  intros * Hb.
  split; intros H.
  - rewrite <- Qmult_inj_r with (x:=a) (y:=c/b) (z:=b); trivial.
    rewrite Qmult_comm with (x:=c/b).
    rewrite Qmult_div_r; trivial.
  - rewrite <- Qmult_inj_r with (x:=a) (y:=c/b) (z:=b) in H; trivial.
    rewrite Qmult_comm with (x:=c/b) in H.
    rewrite Qmult_div_r in H; trivial.
Qed.


Lemma Qdiv_inj: forall a b c, ~ c == 0 -> a == b <-> a/c == b/c.
Proof.
  intros * Hc.
  split; intros Heq.
  - rewrite <- Qmult_inj_l with (z:=c); [rewrite Qmult_div_r; [rewrite Qmult_div_r|]|]; trivial.
  - rewrite <- Qmult_inj_l with (z:=c) in Heq; [rewrite Qmult_div_r in Heq; [rewrite Qmult_div_r in Heq|]|]; trivial.
Qed.


Lemma Qmult_dist_div: forall a b c, c * (a / b) == ((c*a)/b).
Proof.
  intros.
  apply Qeq_sym.
  rewrite Qdiv_mult_inv.
  rewrite <- Qmult_assoc.
  rewrite <- Qdiv_mult_inv.
  reflexivity.
Qed.

Lemma Qsquare: forall a, a ^ 2 == a * a.
Proof.
  intros.
  auto with qarith.
Qed.

Lemma Qdiv_squared: forall a b, (a / b) ^ 2 == (a*a)/(b*b).
Proof.
  intros.
  rewrite Qsquare.
  rewrite Qdiv_mult_inv.
  rewrite Qmult_assoc.
  rewrite <- Qmult_assoc with (n:=a) (m:=/b) (p:=a).
  rewrite Qmult_comm with (x:=/b) (y:=a).
  rewrite Qmult_assoc with (n:=a) (m:=a) (p:=/b).
  rewrite <- Qmult_assoc.
  rewrite <- Qinv_mult_distr.
  reflexivity.
Qed.

Lemma Qdiv_dist_mult: forall a b, a / b  == /(/a*b).
Proof.
  intros.
  rewrite Qinv_mult_distr.
  rewrite Qinv_involutive.
  rewrite Qdiv_mult_inv.
  reflexivity.
Qed.

Lemma Qdiv_div: forall a b c, a / b / c == a/(b*c).
Proof.
  intros.
  rewrite Qdiv_mult_inv.
  rewrite Qdiv_mult_inv.
  rewrite <- Qmult_assoc.
  rewrite <- Qinv_mult_distr.
  rewrite <- Qdiv_mult_inv.
  reflexivity.
Qed.

Lemma Qpoly2_sub_dist: forall a b, (a - b)*(a - b) == a*a - (2#1)*a*b + b*b.
Proof. intros. ring. Qed.



Lemma Qmult_sum2_dist_l: forall a b c, c*(a + b) == a*c + b*c.
Proof. intros. ring. Qed.

Lemma Qmult_sum2_dist_r: forall a b c, (a + b)*c == a*c + b*c.
Proof. intros. ring. Qed.

Lemma Qmult_sub2_dist_l: forall a b c, c*(a - b) == a*c - b*c.
Proof. intros. ring. Qed.

Lemma Qmult_sub2_dist_r: forall a b c, (a - b)*c == a*c - b*c.
Proof. intros. ring. Qed.

Lemma Qdiv_sum2_dist_r: forall a b c, (a + b)/c == a/c + b/c.
Proof.
  intros.
  rewrite Qdiv_mult_inv.
  rewrite Qmult_sum2_dist_r.
  rewrite <- Qdiv_mult_inv.
  rewrite <- Qdiv_mult_inv.
  reflexivity.
Qed.

Lemma Qdiv_diff2_dist_r: forall a b c, (a - b)/c == a/c - b/c.
Proof.
  intros.
  rewrite Qplus_neg.
  rewrite Qplus_neg.
  rewrite Qdiv_sum2_dist_r.
  rewrite Qdiv_neg_l.
  reflexivity.
Qed.


Lemma Qmult_sum3_dist_r: forall a b c d, (a + b + c)*d == a*d + b*d + c*d.
Proof. intros. ring. Qed.

Lemma Qmult_sub_sum3_dist_r: forall a b c d, (a - b + c)*d == a*d - b*d + c*d.
Proof. intros. ring. Qed.

Lemma Qdiv_sub_sum3_dist_r: forall a b c d, (a - b + c)/d == a/d - b/d + c/d.
Proof.
  intros.
  rewrite Qdiv_mult_inv.
  rewrite Qmult_sub_sum3_dist_r.
  rewrite <- Qdiv_mult_inv.
  rewrite <- Qdiv_mult_inv.
  rewrite <- Qdiv_mult_inv.
  reflexivity.
Qed.

Lemma Qdiv_mult3_cancel_1: forall a b c, ~ a == 0 -> (a*b*c)/a == b*c.
Proof.
  intros.
  rewrite Qdiv_mult_inv.
  rewrite <- Qmult_assoc.
  rewrite <- Qmult_comm.
  rewrite Qmult_assoc.
  rewrite <- Qmult_comm.
  rewrite <- Qmult_assoc with (n:=c).
  rewrite  Qmult_comm with (x:=/a) (y:= a).
  rewrite Qmult_inv_r; trivial.
  rewrite Qmult_1_r.
  reflexivity.
Qed.

Lemma Qdiv_mult4_cancel_1: forall a b c d, ~ a == 0 -> (a*b*c*d)/a == b*c*d.
Proof.
  intros.
  rewrite <- Qmult_assoc.
  rewrite Qdiv_mult3_cancel_1; trivial.
  rewrite Qmult_assoc.
  reflexivity.
Qed.



Ltac plus_minus :=
  repeat match goal with
  | |- context[?x + ?y] =>
      match y with
      | context[-x] =>
          match y with
          | -x => rewrite (Qplus_assoc x (-x))
          | -x + _ => rewrite (Qplus_assoc x (-x))
          | ?a + ?z => rewrite (Qplus_assoc x a), (Qplus_comm x a), <- (Qplus_assoc a x)
          end
      end
  end.
Ltac minus_plus :=
  repeat match goal with
  | |- context[-?x + ?y] =>
      match y with
      | context[x] =>
          match y with
          | x => rewrite (Qplus_assoc (-x) x)
          | x + _ => rewrite (Qplus_assoc (-x) x)
          | ?a + ?z => rewrite (Qplus_assoc (-x) a), (Qplus_comm (-x) a), <- (Qplus_assoc a (-x))
          end
      end
  end.
Ltac plus_opp_simpl :=
  first [progress plus_minus | progress minus_plus]; rewrite ?Qplus_opp_l, ?Qplus_opp_r, ?Qplus_0_r, ?Qplus_0_l.



(*Hint Resolve*)

Hint Rewrite
  Qplus_neg
  Qdiv_mult_inv
  Qmult_neg_1
  Qmult_inv_l
  Qplus_double
  Qplus_half
  Qdiv_neg_l
  Qplus_l_equ_sub_r
  Qplus_l_equ_sub_l
  Qplus_r_equ_sub_r
  Qplus_r_equ_sub_l
  Qplus_neg_half_l
  Qmult_l_equ_div_r
  Qdiv_inj
  Qmult_dist_div
  Qsquare
  Qdiv_squared
  Qdiv_dist_mult
  Qdiv_div
  Qpoly2_sub_dist
  Qmult_sum2_dist_l
  Qmult_sum2_dist_r
  Qmult_sub2_dist_l
  Qmult_sub2_dist_r
  Qdiv_sum2_dist_r
  Qdiv_diff2_dist_r
  Qmult_sum3_dist_r
  Qmult_sub_sum3_dist_r
  Qdiv_sub_sum3_dist_r
  Qdiv_mult4_cancel_1
  Qdiv_mult3_cancel_1 : q_math_hints.

Ltac q_math := ring || autorewrite with q_math_hints; auto with qarith.
