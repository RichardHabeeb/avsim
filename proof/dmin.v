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


(** ##############################################################################
MULTISTEP DEFINITIONS/THEOREMS
################################################################################*)
Definition relation (X: Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall(x : X), multi R x x
  | multi_step : forall(x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem multi_R : forall(X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall(X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

Lemma multi_2_step : forall (X : Type) (R : relation X) (c c' c'' : X), R c c' -> R c' c'' -> multi R c c''.
Proof.
  intros.
  apply multi_step with c'. trivial.
  apply multi_step with c''; trivial.
  apply multi_refl.
Qed.

Lemma multi_trans_l : forall (X : Type) (R : relation X) (c c' c'' : X), multi R c c' -> R c' c'' -> multi R c c''.
Proof.
  intros X R c c' c'' mS S.
  induction mS.
  - apply multi_step with (z:=c'') in S; trivial.
    apply multi_refl.
  - apply multi_step with y; trivial.
    apply IHmS; trivial.
Qed.

Lemma multi_trans_r : forall (X : Type) (R : relation X) (c c' c'' : X), R c c' -> multi R c' c'' -> multi R c c''.
Proof.
  intros.
  apply multi_step with c'; trivial.
Qed.




(** ##############################################################################
DEFINITIONS 
################################################################################*)


Section RoadContext.

Record car_st := {
  c_x : Q;
  c_v : Q;
  c_a : Q;
  c_l : Q;
  c_lane : nat;
}.

Definition equ_car_st (c c' :car_st) :=
  (c_x c) == (c_x c') /\
  (c_v c) == (c_v c') /\
  (c_a c) == (c_a c') /\
  (c_l c) == (c_l c') /\
  (c_lane c) = (c_lane c').

Definition non_acc_equ_state (c1 c2 : car_st) := 
  (c_x c1 == c_x c2) /\
  (c_v c1 == c_v c2) /\
  (c_l c1 == c_l c2) /\
  (c_lane c1 = c_lane c2).

Definition acc_choice (c : car_st) (a : Q) := (Build_car_st (c_x c) (c_v c) a (c_l c) (c_lane c)).
Definition acc_choice_p_snd (c : car_st*car_st) (a : Q) :=
  ((fst c), (Build_car_st (c_x (snd c)) (c_v (snd c)) a (c_l (snd c)) (c_lane (snd c)))).


Variables dt a_max a_min a_br_req : Q.

Hypothesis PosT : dt > 0.
Hypothesis BrakeReq : a_br_req < 0.
Hypothesis BrakeMax : a_min <= a_br_req.
Hypothesis AccMax : a_max > 0.
Hypothesis PosLen: forall c:car_st, 0 < c_l c.

Definition c_rear_x (c : car_st) := (c_x c) - (c_l c).

Definition same_lane (c1 c2 : car_st) := (c_lane c1 = c_lane c2).
Definition same_lane_p (c : car_st*car_st) := (c_lane (fst c) = c_lane (snd c)).

Definition step (c : car_st) (c' : car_st) :=
  (* Kinematics *)
  (c_x c' == (c_x c) + (c_v c)*dt + ((c_a c)*(dt^2)/(2#1))) /\ 
  (c_v c' == (c_v c) + (c_a c)*dt) /\
  (* Bounded acceleration *)
  (a_min <= (c_a c) <= a_max) /\
  (a_min <= (c_a c') <= a_max) /\
  (* No reverse driving *)
  ((c_v c) >= 0) /\ ((c_v c') >= 0) /\
  (c_x c <= c_x c') /\
  (* Single lane (for now) *)
  (same_lane c c') /\
  (* Constant/Positive length *)
  (c_l c == c_l c').

Definition const_acc (c c' : car_st) := (forall c'', multi step c c'' -> multi step c'' c' -> c_a c == c_a c'').


Definition parallel_step (c c': car_st*car_st ) := step (fst c) (fst c') /\ step (snd c) (snd c').
(*   let (cf, cr) := c in let (cf', cr') := c' in step cf cf' /\ step cr cr'. *)

Definition front (c : car_st*car_st) := fst c.
Definition rear (c : car_st*car_st) := snd c.


Definition collision (c1 : car_st) (c2 : car_st) :=
  (same_lane c1 c2) /\
  ((c_x c1 >= c_rear_x c2) /\ (c_x c1 <= c_x c2) \/
   (c_x c2 >= c_rear_x c1) /\ (c_x c2 <= c_x c1)).

Definition collision_free_step (c1 c1' c2 c2' : car_st) :=
  ~(collision c1 c2) /\ (same_lane c1 c2) /\
  (step c1 c1') /\ (step c2 c2') /\
  ~(collision c1' c2') /\
  (c_x c1 < c_x c2 -> c_x c1' < c_x c2') /\ (* Relative orderings must be the same, no instantaneous passing *)
  (c_x c2 < c_x c1 -> c_x c2' < c_x c1').
Definition collision_free_step_p (c c' : car_st*car_st) := collision_free_step (fst c) (fst c') (snd c) (snd c').


Definition max_stopping_dist (c : car_st) := -((c_v c + a_max*dt)^2)/((2#1)*a_br_req).
Definition min_stopping_dist (c : car_st) := -((c_v c)^2)/((2#1)*a_min).

Definition d_min_holds (cf cr : car_st) :=
  (c_rear_x cf) > (c_x cr) /\ (* This is implied by the following but it's here for convenience *)
  (c_rear_x cf) - (c_x cr) > ((c_v cr)*dt + a_max*dt^2/(2#1)) /\
  (c_rear_x cf) - (c_x cr) > 
  (c_v cr)*dt + a_max*dt^2/(2#1) + max_stopping_dist cr - min_stopping_dist cf.



Definition d_min_holds_p (c : car_st*car_st) := d_min_holds (front c) (rear c).
Definition d_min_step (c c' : car_st*car_st) :=
  (~ d_min_holds_p c -> c_a (rear c) <= a_br_req) /\ parallel_step c c'.
Definition d_min_false_multi (c c' : car_st*car_st) := 
  (forall c'', multi d_min_step c c'' -> multi d_min_step c'' c' -> ~ d_min_holds_p c').

Definition collision_free_multi_dmin_step (c c' : car_st*car_st) :=
  ~(collision (fst c) (snd c)) /\ 
  (multi d_min_step c c') /\
  (forall c'', multi d_min_step c c'' -> multi d_min_step c'' c' -> same_lane (fst c'') (snd c'') ->
    (~(collision (fst c'') (snd c'')) /\
      (c_x (fst c) < c_x (snd c) -> c_x (fst c'') < c_x (snd c'')) /\ (* Relative orderings must be the same, no instantaneous passing *)
      (c_x (snd c) < c_x (fst c) -> c_x (snd c'') < c_x (fst c'')))).



(** ##############################################################################
MOTION THEOREMS 
################################################################################*)

Lemma no_reverse_driving : forall (c : car_st) (c' : car_st), (step c c') -> (c_x c <= c_x c').
Proof.
  intros.
  unfold step in H.
  intuition.
Qed.

Lemma multi_no_reverse_driving : forall (c c' : car_st), (multi step c c') -> (c_x c <= c_x c').
Proof.
  intros c c' H.
  induction H.
  - apply Qle_refl.
  - apply no_reverse_driving in H.
    apply Qle_trans with (y:= c_x y); assumption.
Qed.

Lemma no_reverse_driving_rear : forall (c : car_st) (c' : car_st), (step c c') -> (c_rear_x c <= c_rear_x c').
Proof.
  intros.
  unfold step in H.
  unfold c_rear_x.
  rewrite !Qplus_neg.
  intuition.
  rewrite H10.
  apply Qplus_le_compat; auto with qarith.
Qed.

Lemma car_order_rear_weakening: forall (cf cr : car_st), c_x cr < c_rear_x cf -> c_x cr < c_x cf.
Proof.
  intros * Hr.
  unfold c_rear_x in Hr.
  apply Qlt_trans with (y:=c_x cf - c_l cf); trivial.
  apply Qplus_lt_r with (z:=-c_x cf).
  rewrite !Qplus_neg.
  rewrite Qplus_assoc.
  rewrite !Qplus_opp_l.
  rewrite Qplus_0_l.
  assert (0 < c_l cf) as Hl; trivial.
  rewrite <- Qneg_0.
  apply Qopp_lt_compat; trivial.
Qed.


Lemma car_rear_lt: forall (c : car_st), c_rear_x c < c_x c.
Proof.
  intros.
  unfold c_rear_x.
  apply Qplus_lt_r with (z:=-c_x c).
  rewrite !Qplus_neg.
  rewrite Qplus_assoc.
  rewrite !Qplus_opp_l.
  rewrite Qplus_0_l.
  assert (0 < c_l c) as Hl; trivial.
  rewrite <- Qneg_0.
  apply Qopp_lt_compat; trivial.
Qed.

Lemma car_rear_lt_false: forall (c : car_st), c_x c < c_rear_x c -> False.
Proof.
  intros * H.
  assert (c_rear_x c < c_x c) as H0 by apply car_rear_lt.
  apply Qlt_not_lt in H.
  contradiction.
Qed.

Lemma dt_squared_pos: 0 < dt^2.
Proof.
  rewrite Qsquare.
  rewrite <- Qmult_0_l with (x:=dt).
  apply Qmult_lt_compat_r; trivial.
Qed.

Lemma dt_squared_nonneg: 0 <= dt^2.
Proof.
  apply Qlt_le_weak in PosT.
  rewrite Qsquare.
  apply Qmult_le_0_compat; trivial.
Qed.

Lemma a_max_term_pos: 0 <= a_max*dt^2/(2#1).
Proof.
  assert (0 <= dt^2) as A1 by apply dt_squared_nonneg.
  rewrite Qdiv_mult_inv.
  apply Qmult_le_0_compat; auto with qarith.
  apply Qmult_le_0_compat; [apply Qlt_le_weak in AccMax|]; trivial.
Qed.

Lemma partial_const_acc: forall (c c' c'' : car_st), 
  const_acc c c'' -> multi step c c' -> multi step c' c'' -> const_acc c' c''.
Proof.
  intros * Aconst MStep1 MStep2.
  unfold const_acc in Aconst.
  unfold const_acc.
  intros.
  apply multi_trans with (z:=c''0) in MStep1 as MStepBig; trivial.
  apply Aconst in MStepBig; trivial.
  apply Aconst in MStep1; trivial.
  rewrite <- MStep1; trivial.
Qed.


Lemma step_dist: forall (c c' : car_st), 
  step c c' -> ~ c_a c == 0 -> (c_x c' - c_x c) == (c_v c' ^ 2 - c_v c ^ 2) / ((2#1)*c_a c).
Proof.
  intros * S Anz.
  unfold step in S.
  intuition.

  rewrite Qplus_comm in H1.
  apply Qplus_r_equ_sub_r in H1 as T0.
  apply Qeq_sym in T0.
  rewrite Qmult_comm in T0.
  rewrite Qmult_l_equ_div_r in T0; try auto with qarith.

  rewrite <- Qplus_assoc in H.
  apply Qplus_r_equ_sub_l in H as U0.
  rewrite T0 in U0.

  rewrite Qmult_dist_div with (a:=(c_v c' - c_v c)) (b:=c_a c) (c:=c_v c) in U0.
  rewrite Qdiv_squared in U0.
  rewrite Qmult_dist_div with (c:=c_a c) in U0.

  rewrite Qmult_comm with (x:=c_a c) (y:=(c_v c' - c_v c) * (c_v c' - c_v c)) in U0.
  rewrite Qdiv_mult_inv with (b:=c_a c * c_a c) in U0.
  
  rewrite <- Qmult_assoc in U0.
  rewrite <- Qdiv_mult_inv with (b:=c_a c * c_a c) in U0.
  rewrite Qdiv_dist_mult with (a:=c_a c) in U0.
  rewrite Qmult_assoc with (n:=/c_a c) in U0.
  rewrite Qmult_comm with (x:=/c_a c) in U0.
  rewrite Qmult_inv_r in U0; trivial.
  rewrite Qmult_1_l in U0.

  rewrite Qpoly2_sub_dist in U0.
  rewrite Qmult_sub_sum3_dist_r in U0.

  rewrite Qmult_sub2_dist_l in U0.
  rewrite Qdiv_diff2_dist_r in U0.
  rewrite Qdiv_sub_sum3_dist_r in U0.
  rewrite Qdiv_mult4_cancel_1 in U0; [|unfold Qeq]; auto with qarith.
  rewrite <- !Qsquare in U0.
  rewrite !Qplus_neg in U0.

  rewrite Qplus_comm with (x:=c_v c' ^ 2 * / c_a c / (2 # 1)) in U0.
  rewrite Qplus_assoc in U0.
  rewrite Qplus_assoc in U0.
  rewrite Qplus_comm with (x:=c_v c' * c_v c / c_a c) in U0.
  rewrite <- Qplus_assoc with (z:=- (c_v c' * c_v c * / c_a c)) in U0.
  rewrite Qplus_opp_r in U0.
  rewrite Qplus_0_r in U0.

  rewrite Qplus_comm with (x:=- (c_v c ^ 2 / c_a c)) in U0.
  rewrite <- Qplus_assoc in U0.
  rewrite Qplus_neg_half_l in U0.

  rewrite <- Qplus_neg in U0.
  rewrite <- Qplus_neg in U0.

  rewrite <- Qdiv_diff2_dist_r in U0.
  rewrite <- Qdiv_mult_inv in U0.
  rewrite <- Qdiv_diff2_dist_r in U0.
  rewrite Qdiv_div in U0.
  rewrite Qmult_comm in U0.
  exact U0.
Qed.


Lemma multi_step_dist: forall (c c' : car_st), 
  multi step c c' -> ~ c_a c == 0 -> const_acc c c' -> 
  (c_x c' - c_x c) == (c_v c' ^ 2 - c_v c ^ 2) / ((2#1)*c_a c).
Proof.
  intros * MSfull Anz AConst.
  induction MSfull.
  - rewrite !Qplus_neg.
    rewrite !Qplus_opp_r.
    rewrite Qdiv_mult_inv.
    rewrite Qmult_0_l.
    reflexivity.
  - apply step_dist in H as D0.
    apply multi_R in H as HMS.
    apply AConst in HMS as G0.
    assert (~ c_a y == 0) as G1.
    {
      rewrite <- G0; assumption.
    }
    apply IHMSfull in G1.
    + apply Qeq_sym in D0 as D1.
      rewrite <- Qplus_l_equ_sub_r in D1.
      rewrite <- D1 in G1.
      apply Qeq_sym in G1.
      rewrite <- Qplus_l_equ_sub_r in G1.
      rewrite !Qplus_assoc in G1.
      rewrite <- G0 in G1; trivial.
      rewrite !Qplus_neg in G1.
      rewrite <- Qdiv_sum2_dist_r in G1.
      rewrite !Qplus_assoc in G1.
      rewrite <- Qplus_assoc with (y:=- c_v y ^ 2) in G1.
      rewrite Qplus_opp_l in G1.
      rewrite Qplus_0_r in G1.
      rewrite Qplus_l_equ_sub_r in G1.
      apply Qeq_sym in G1.
      assumption.
    + apply partial_const_acc with (c':=y) in AConst; trivial.
    + assumption.
Qed.


Lemma faster_car_bigger_step : forall (c1 : car_st) (c1' : car_st) (c2 : car_st) (c2' : car_st),
  (c_v c1 >= c_v c2) -> (c_a c1 >= c_a c2) ->
  (step c1 c1') -> (step c2 c2') ->
  (c_x c1' - c_x c1 >= c_x c2' - c_x c2).
Proof.
  intros c1 c1' c2 c2' v_fast a_fast step1 step2.
  unfold step in step1.
  unfold step in step2.
  intuition.
  rewrite H.
  rewrite H1.

  rewrite !Qplus_neg.
  rewrite <- !Qplus_assoc.
  plus_opp_simpl.

  rewrite !Qsquare.
  rewrite !Qmult_assoc.

  assert (c_v c2 * dt <= c_v c1 * dt).
  {
    apply Qmult_le_compat_r; [| apply Qlt_le_weak]; trivial.
  }
  assert (c_a c2 * dt * dt / (2 # 1) <= c_a c1 * dt * dt / (2 # 1)).
  {
    apply Qmult_le_compat_r; auto with qarith.
    apply Qmult_le_compat_r; [| apply Qlt_le_weak]; trivial.
    apply Qmult_le_compat_r; [| apply Qlt_le_weak]; trivial.
  } 
  apply Qplus_le_compat; assumption.
Qed.


Lemma parallel_step_fst : forall (c c' : car_st*car_st), 
  parallel_step c c' -> step (fst c) (fst c').
Proof.
  intros * PStep.
  unfold parallel_step in PStep.
  intuition.
Qed.

Lemma parallel_step_snd : forall (c c' : car_st*car_st), 
  parallel_step c c' -> step (snd c) (snd c').
Proof.
  intros * PStep.
  unfold parallel_step in PStep.
  intuition.
Qed.

Lemma multi_parallel_multi_step_fst : forall (c c' : car_st*car_st), 
  multi parallel_step c c' -> multi step (fst c) (fst c').
Proof.
  intros * MPStep.
  induction MPStep.
  - apply multi_refl.
  - unfold parallel_step in H.
    intuition.
    apply multi_R in H0.
    apply multi_trans with (y:=(fst y)); trivial.
Qed.

Lemma multi_parallel_multi_step_snd : forall (c c' : car_st*car_st), 
  multi parallel_step c c' -> multi step (snd c) (snd c').
Proof.
  intros * MPStep.
  induction MPStep.
  - apply multi_refl.
  - unfold parallel_step in H.
    intuition.
    apply multi_R in H1.
    apply multi_trans with (y:=(snd y)); trivial.
Qed.




(*
Lemma faster_car_bigger_const_multi_step : forall (c c' : car_st*car_st),
  c_v (snd c) <= c_v (fst c) -> 
  c_a (snd c) <= c_a (fst c) ->
  multi parallel_step c c' ->
  const_acc (fst c) (fst c') ->
  const_acc (snd c) (snd c') ->
  c_x (snd c') - c_x (snd c) <= c_x (fst c') - c_x (fst c) .
Proof.
  intros * VFaster AFaster MPStep AConst1 AConst2.

  induction MPStep.
  - rewrite !Qplus_neg, !Qplus_opp_r.
    auto with qarith.
  - assert (multi step (fst y) (fst z)) as MStepYZFst.
    { apply multi_parallel_multi_step_fst; trivial. }
    assert (multi step (snd y) (snd z)) as MStepYZSnd.
    { apply multi_parallel_multi_step_snd; trivial. }

    apply multi_step with (z0:=z) in H as MPStepXZ; trivial.
    assert (multi step (fst x) (fst z)) as MStepXZFst.
    { apply multi_parallel_multi_step_fst; trivial. }
    assert (multi step (snd x) (snd z)) as MStepXZSnd.
    { apply multi_parallel_multi_step_snd; trivial. }
    
    apply parallel_step_fst in H as StepFstXY.
    apply parallel_step_snd in H as StepSndXY.
    apply multi_R in StepFstXY as MStepFstXY.
    apply multi_R in StepSndXY as MStepSndXY.
    apply partial_const_acc with (c':=fst y) in AConst1 as AConstY1; trivial.
    apply partial_const_acc with (c':=snd y) in AConst2 as AConstY2; trivial.

    assert (c_a (snd y) <= c_a (fst y)).
    {
      
    }
    
Qed.
*)

Lemma step_min_dist: forall (c c' cm cm' : car_st), 
  non_acc_equ_state c cm -> c_a cm == a_min -> step c c' -> step cm cm' -> (c_x cm' <= c_x c').
Proof.
  intros * Eq Amin S Sm.

  assert (step c c') as S0 by trivial.
  unfold step in S0.
  unfold non_acc_equ_state in Eq.
  intuition.
  assert(c_v cm <= c_v c) as Vweak.
  {
    rewrite H3; auto with qarith.
  }
  assert(c_a cm <= c_a c) as Aweak.
  {
    rewrite <- Amin in *; trivial.
  }
  apply Qplus_le_l with (z:=- c_x cm); auto with qarith.
  rewrite <- 1 H at 2.
  apply faster_car_bigger_step; trivial.
Qed.


Lemma d_min_holds_no_inst_collision : forall (cf cr : car_st),
  d_min_holds cf cr -> same_lane cf cr -> ~ collision cf cr.
Proof.
  intros * InitD Lane.
    unfold d_min_holds in InitD.
    unfold collision.
    intuition.
    + apply Qle_lt_trans with (x:=c_x cf) (y:=c_x cr) (z:=c_rear_x cf) in H5 as A0; trivial.
      assert (c_rear_x cf < c_x cf) as A1 by apply car_rear_lt.
      apply Qlt_not_lt in A1.
      contradiction.
    + apply Qlt_not_le in H0.
      contradiction.
Qed.

Lemma d_min_holds_ordering : forall (c : car_st*car_st),
  d_min_holds_p c -> c_x (rear c) < c_x (front c).
Proof.
  intros * H.
  unfold d_min_holds_p, d_min_holds in H.
  destruct H as (H0 & H).
  apply car_order_rear_weakening in H0; trivial.
Qed.


Lemma d_min_holds_collision_free_step : forall (cf cf' cr cr' : car_st),
  d_min_holds cf cr -> same_lane cf cr -> step cf cf' -> step cr cr' -> collision_free_step cf cf' cr cr'.
Proof.
  intros * init_d_min lane stepf stepr.
  unfold collision_free_step.
  split.
  {
    apply d_min_holds_no_inst_collision; trivial.
  }
  split; trivial.
  split; trivial.
  split; trivial.

  unfold d_min_holds in init_d_min.
  unfold step in stepf.
  unfold step in stepr.

  assert (0 <= c_v cr * dt) as A0.
  {
    unfold step in stepr.
    intuition.
    apply Qmult_le_0_compat; trivial.
    apply Qlt_le_weak in PosT; trivial.
  }

  assert (0 <= dt^2) as A1 by apply dt_squared_nonneg.
  assert (0 <= a_max*dt^2/(2#1)) as A2 by apply a_max_term_pos.


  apply Qplus_le_compat with (t:=a_max*dt^2/(2#1)) (z:=0) in A0; trivial.
  rewrite Qplus_0_l in A0.

  assert (c_rear_x cf' - c_x cr' > 0) as A3.
  {
    intuition.
    rewrite H3.
    rewrite Qplus_neg.
    apply Qlt_minus_iff with (q:=c_rear_x cf').
    rewrite <- Qplus_assoc.
    apply Qplus_l_lt_sub_l.
    apply Qlt_r_sub_le_weak_l with (a:=c_rear_x cf).
    - apply Qlt_l_plus_le_weak_r with (b:=a_max * dt ^ 2 / (2 # 1)); trivial.
      apply Qmult_le_compat_r; auto with qarith.
      apply Qmult_le_compat_r; auto with qarith.
    - unfold c_rear_x.
      rewrite !Qplus_neg.
      rewrite H23.
      rewrite Qplus_le_l; trivial.
  }

  apply Qlt_minus_iff in A3.
  apply car_order_rear_weakening in A3 as A4.
  apply Qlt_not_le in A3 as A5.
  apply Qlt_not_le in A4 as A6.

  split.
  {
    unfold collision.
    intuition.
  }
  split; trivial.
  intros C.
  intuition.
  apply car_order_rear_weakening in H.
  apply Qlt_not_lt in H.
  contradiction.
Qed.


Lemma d_min_holds_response_dist : forall (c c' : car_st*car_st),
  d_min_holds_p c -> d_min_step c c' -> 
    (c_rear_x (front c') - c_x (rear c') > (max_stopping_dist (rear c) - min_stopping_dist (front c))).
Proof.
  intros * InitDMin DStep.
  unfold d_min_holds_p in InitDMin.
  unfold d_min_holds in InitDMin.
  unfold d_min_step in DStep.
  unfold parallel_step in DStep.
  unfold front in *.
  unfold rear in *.
  destruct DStep as (DMinInv & StepF & StepR).
  apply no_reverse_driving_rear in StepF as fRearDiff.
  unfold step in *.
  apply Qplus_l_lt_sub_l with (a:=c_x (snd c')).
  destruct StepR as [K0 StepR].
  rewrite K0.
  rewrite <- !Qplus_assoc.
  apply Qplus_l_lt_sub_l with (a:=c_x (snd c)).
  rewrite !Qplus_neg, !Qplus_assoc.
  apply Qlt_r_plus_le_weak_l with (a:=c_rear_x (fst c)); trivial.
  rewrite Qplus_comm with (y:=c_a (snd c) * dt ^ 2 / (2 # 1)).
  rewrite <- !Qplus_assoc.
  apply Qlt_l_plus_le_weak_l with (a:=a_max * dt ^ 2 / (2 # 1)).
  - rewrite !Qplus_assoc, <- !Qplus_neg.
    rewrite Qplus_comm with (x:=a_max * dt ^ 2 / (2 # 1)).
    intuition.
  - rewrite !Qsquare, !Qdiv_mult_inv, !Qmult_assoc.
    repeat apply Qmult_le_compat_r; auto with qarith.
    intuition.
Qed.



Lemma same_lane_refl : forall (c : car_st), same_lane c c.
Proof.
  intros.
  unfold same_lane.
  reflexivity.
Qed.

Lemma same_lane_trans : forall (c c' c'' : car_st), same_lane c c' -> same_lane c' c'' -> same_lane c c''.
Proof.
  intros * L1 L2.
  unfold same_lane in *.
  rewrite L1, L2.
  reflexivity.
Qed.

Lemma step_same_lane : forall (c c' : car_st),
  step c c' -> same_lane c c'.
Proof.
  intros * Step.
  unfold step in Step.
  intuition.
Qed.

(* This will have to be relaxed somehow *)
Lemma multi_step_same_lane : forall (c c' : car_st),
  multi step c c' -> same_lane c c'.
Proof.
  intros * MStep.
  induction MStep.
  - apply same_lane_refl.
  - apply step_same_lane in H.
    apply same_lane_trans with (c':=y); trivial.
Qed.

Lemma d_min_step_fst : forall (c c' : car_st*car_st),
  d_min_step c c' -> step (fst c) (fst c').
Proof.
  intros * DStep.
  unfold d_min_step in DStep.
  unfold parallel_step in DStep.
  intuition.
Qed.

Lemma d_min_step_snd : forall (c c' : car_st*car_st),
  d_min_step c c' -> step (snd c) (snd c').
Proof.
  intros * DStep.
  unfold d_min_step in DStep.
  unfold parallel_step in DStep.
  intuition.
Qed.


Lemma multi_d_min_step_multi_step_fst : forall (c c' : car_st*car_st),
  multi d_min_step c c' -> multi step (fst c) (fst c').
Proof.
  intros * MDStep.
  induction MDStep.
  - apply multi_refl.
  - apply d_min_step_fst in H.
    apply multi_R in H.
    apply multi_trans with (y:=(fst y)); trivial.
Qed.

Lemma multi_d_min_step_multi_step_snd : forall (c c' : car_st*car_st),
  multi d_min_step c c' -> multi step (snd c) (snd c').
Proof.
  intros * MDStep.
  induction MDStep.
  - apply multi_refl.
  - apply d_min_step_snd in H.
    apply multi_R in H.
    apply multi_trans with (y:=(snd y)); trivial.
Qed.


Lemma d_min_init_no_collision : forall (c : car_st*car_st), (d_min_holds_p c) -> ~ collision (fst c) (snd c).
Proof.
  intros * InitDMin.
  unfold d_min_holds_p in InitDMin.
  unfold d_min_holds in InitDMin.
  unfold collision.
  intro G.
  destruct InitDMin as (InitOrder & InitDMin).
  unfold front,rear in *.
  destruct G as (L & [[E0 E1] | [E0 E1]]).
  - apply Qle_lt_trans with (z:=c_rear_x (fst c)) in E1; trivial.
    now (apply car_rear_lt_false in E1).
  - apply Qlt_le_trans with (z:=c_x (snd c)) in InitOrder; trivial.
    apply Qlt_irrefl in InitOrder.
    contradiction.
Qed.


Lemma multi_dmin_step_multi_parallel_step : forall (c c' : car_st*car_st), 
  multi d_min_step c c' -> multi parallel_step c c'.
Proof.
  intros * MDStep.
  induction MDStep.
  - apply multi_refl.
  - unfold d_min_step in H.
    intuition.
    apply multi_R in H1.
    apply multi_trans with (y:=y); trivial.
Qed.


Definition d_min_brake_mode (c c'' : car_st*car_st) :=
  (forall (c' : car_st*car_st), multi d_min_step c c' -> multi d_min_step c' c'' -> ~ d_min_holds_p c').

Lemma d_min_transition_invariant : forall (c c' : car_st*car_st),
  (d_min_holds_p c) -> same_lane (fst c) (snd c) -> multi d_min_step c c' -> ~(d_min_holds_p c') ->
  (exists (i i' : car_st*car_st),
    multi d_min_step c i /\
    d_min_step i i' /\
    multi d_min_step i' c' /\ 
    d_min_holds_p i /\
    d_min_brake_mode i' c').
Proof.
Admitted.



Definition d_min_step_rear_bound_acc (c c' : car_st*car_st) (a : Q) := 
  (forall c'', multi d_min_step c c'' -> multi d_min_step c'' c' -> c_a (rear c'') <= a).

(* Lemma step_min_dist: forall (c c' cm cm' : car_st), 
  non_acc_equ_state c cm -> c_a cm == a_min -> step c c' -> step cm cm' -> (c_x cm' <= c_x c').
Proof. *)



(* Lemma multi_d_min_step_dist_bound: forall (c1 c1' c2 c2' : car_st*car_st), 
  multi d_min_step c1 c1' -> multi d_min_step c2 c2' ->
  non_acc_equ_state (rear c1) (rear c2) -> (front c1) = (front c2) -> (front c1') = (front c2') ->
  const_acc (rear c2) (rear c2') -> c_a (rear c2) == a_br_req -> 
  d_min_brake_mode c1 c1' ->
  c_x (rear c1') - c_x (rear c1) <= c_x (rear c2') - c_x (rear c2).
Proof.
  intros * MDStep1 MDStep2 EQR EQF1 EQF2 ConstAcc InitAcc BrakeMode.
  apply multi_d_min_step_multi_step_snd in MDStep2 as MStep2R.
  SearchAbout (const_acc).
  unfold front,rear in *.
  apply multi_step_dist in MStep2R as D0; trivial.
Admitted. *)

Definition d_min_compare_step (c1 c2 : (car_st*car_st)*(car_st*car_st)) :=
  d_min_step (fst c1) (fst c2) /\ d_min_step (snd c1) (snd c2).

Definition d_min_compare_const_front (c c'': (car_st*car_st)*(car_st*car_st)) :=
  forall (c': (car_st*car_st)*(car_st*car_st)), 
    multi d_min_compare_step c c' -> multi d_min_compare_step c' c'' -> (front (fst c')) = (front (snd c')).


(* Lemma multi_R_alt_path : forall (c c' : car_st),
  multi step c c' -> 
  (exists (d d' : car_st), multi step d d' /\ non_acc_equ_state c d).
Proof.
  intros * MS.
  eexists.
  eexists.
  split.
  - apply MS.
  - unfold non_acc_equ_state.
    intuition.
Qed.

Lemma multi_d_min_step_alt_path : forall (c c' : car_st*car_st),
  multi d_min_step c c' ->
  (exists (d d' : car_st*car_st),
    multi d_min_step d d' /\
    non_acc_equ_state (rear c) (rear d)).
Proof.
  intros * MDStep0.
  eexists.
  eexists.
  split.
  - apply MDStep0.
  - unfold non_acc_equ_state.
    intuition.
Qed. *)


(* Lemma alt_acc_state : forall (c : car_st) (a : Q),
  (exists (d : car_st), c_a d == a /\ non_acc_equ_state c d).
Proof.
  intros *.

  Check Build_car_st.
(*   c_x : Q;
  c_v : Q;
  c_a : Q;
  c_l : Q;
  c_lane : nat;
  c_ts : nat; *)
  exists (Build_car_st (c_x c) (c_v c) a (c_l c) (c_lane c) (c_ts c)).

  unfold non_acc_equ_state.
  simpl.
  repeat split; try reflexivity.
Qed.
 *)

(* Lemma multi_d_min_step_alt_path_br_req : forall (c c' : car_st*car_st),
  multi d_min_step c c' ->
  (exists (d d' : car_st*car_st),
    multi d_min_step d d' /\
    non_acc_equ_state (rear c) (rear d) /\
    const_acc (rear d) (rear d') /\
    c_a (rear d) == a_br_req).
Proof.
  intros * MDStep0.
  eexists.
  eexists.
  eexists.
  - admit.
  - eexists.
    eexists.
  repeat eexists.
Qed. *)



Lemma alt_acc_choice : forall (c : car_st) (a : Q), non_acc_equ_state c (acc_choice c a).
Proof.
  intros *.
  unfold non_acc_equ_state, acc_choice.
  repeat split; reflexivity.
Qed.

Lemma alt_acc_choice_p_snd : forall (c : car_st*car_st) (a : Q), 
  non_acc_equ_state (snd c) (snd (acc_choice_p_snd c a)) /\ (fst c) = (fst (acc_choice_p_snd c a)).
Proof.
  intros *.
  unfold non_acc_equ_state,acc_choice_p_snd.
  repeat split; reflexivity.
Qed.


Lemma can_multi_dmin_step : forall  (c : car_st*car_st),
  (exists (c' : car_st*car_st), multi d_min_step c c').
Proof.
  intros *.
  exists c.
  apply multi_refl.
Qed.

Definition state_within_bounds (c: car_st) :=
  a_min <= c_a c <= a_max /\
  0 <= c_v c /\
  0 <= c_v c + c_a c * dt /\
  c_x c <= c_x c + c_v c * dt + c_a c * (dt * dt) / (2 # 1).

Definition scenario_within_bounds (c: car_st*car_st) :=
  state_within_bounds (fst c) /\ state_within_bounds (snd c).

Lemma can_step : forall (c: car_st), 
  state_within_bounds c -> (exists c' : car_st, step c c').
Proof.
  intros.
  unfold step.
  exists (Build_car_st
    (c_x c + c_v c * dt + c_a c * dt ^ 2 / (2 # 1))
    (c_v c + c_a c * dt)
    0
    (c_l c)
    (c_lane c)).
  unfold same_lane.
  unfold state_within_bounds in H.
  simpl.
  intuition.
  apply Qle_lt_trans with (z:=0) in BrakeMax; auto with qarith.
Qed.

Lemma can_dmin_step : forall  (c : car_st*car_st),
  scenario_within_bounds c ->
  (~ d_min_holds_p c -> c_a (rear c) <= a_br_req) ->
  (exists (c' : car_st*car_st), d_min_step c c').
Proof.
  intros * B.
  unfold scenario_within_bounds in B.
  destruct B as [FB SB].
  apply can_step in FB.
  apply can_step in SB.
  destruct FB as [fc' Sf].
  destruct SB as [sc' Ss].
  pose (c':=(fc',sc')).
  exists c'.
  unfold d_min_step.
  split; trivial.
  unfold parallel_step.
  split; auto.
Qed.



Lemma step_no_loop : forall (c c' : car_st), step c c' -> step c' c -> equ_car_st c c'.
Proof.
  intros * S0 S1.
  apply no_reverse_driving in S0 as E0.
  apply Qle_antisym in E0; [|apply no_reverse_driving in S1; trivial].

  assert (- c_a c' == c_a c) as E1.
  {
    unfold step in *.
    destruct S0 as (D0 & V0 & S0).
    destruct S1 as (D1 & V1 & S1).

    rewrite E0, <- Qplus_assoc, Qplus_r_equ_sub_l, Qplus_neg, Qplus_opp_r in D0,D1.
    rewrite V0, <- Qplus_assoc, Qplus_r_equ_sub_l, Qplus_neg, Qplus_opp_r in V1.

    rewrite <- Qmult_plus_distr_l, Qdiv_inj with (c:=dt) in V1; auto with qarith.
    rewrite Qdiv_mult_l, Qdiv_mult_inv, Qmult_0_l in V1; auto with qarith.

    apply Qplus_inj_r with (z:=- c_a c') in V1.
    rewrite <- Qplus_assoc, Qplus_opp_r, Qplus_0_r, Qplus_0_l in V1.
    assumption.
  }

  assert (- c_v c' == c_v c) as E2.
  {
    unfold step in *.
    destruct S0 as (D0 & V0 & S0).
    destruct S1 as (D1 & V1 & S1).
    rewrite E0, <- Qplus_assoc, Qplus_r_equ_sub_l, Qplus_neg, Qplus_opp_r in D0,D1.
    apply Qplus_r_equ_sub_r in D1.
    rewrite Qplus_neg, Qplus_0_l in D1.
    rewrite Qdiv_mult_inv, <- Qmult_assoc, <- Qmult_neg_l, Qmult_assoc, <- Qdiv_mult_inv in D1.
    rewrite E1 in D1.
    rewrite D1, <- Qmult_sum2_dist_r in D0.
    apply Qeq_sym in D0.
    apply Qmult_eq_0_l in D0; trivial.
    apply Qplus_inj_r with (z:=- c_v c') in D0.
    rewrite <- Qplus_assoc, Qplus_opp_r, Qplus_0_r, Qplus_0_l in D0.
    apply Qeq_sym; trivial.
  }

  assert (c_a c > 0 -> c_v c' > c_v c) as C0.
  {
    intros.
    unfold step in S0.
    destruct S0 as (D0 & V0 & S0).
    rewrite V0.
    apply Qplus_lt_l with (z:=-c_v c).
    rewrite Qplus_comm with (y:=c_a c * dt), <- !Qplus_assoc, !Qplus_opp_r, Qplus_0_r.
    apply Qmult_0_lt; trivial.
  }

  assert (c_a c' > 0 -> c_v c > c_v c') as C1.
  {
    intros.
    unfold step in S1.
    destruct S1 as (D1 & V1 & S1).
    rewrite V1.
    apply Qplus_lt_l with (z:=-c_v c').
    rewrite Qplus_comm with (y:=c_a c' * dt), <- !Qplus_assoc, !Qplus_opp_r, Qplus_0_r.
    apply Qmult_0_lt; trivial.
  }

  assert (c_v c == 0) as E3.
  {
    destruct (Q_dec (c_a c) 0) as [[? | ?] | H].
    - rewrite <- E1 in q.
      apply Qopp_lt_compat in q.
      rewrite Qopp_opp, Qneg_0 in q.
      apply C1 in q as ?.
      unfold step in S0.
      destruct S0 as (D0 & V0 & A0 & A0' & NN0 & NN0' & S0).
      apply Qle_not_lt in NN0' as E3.
      apply Qle_lt_trans with (z:=c_v c) in NN0' as E4; trivial.
      rewrite <- E2 in E4.
      apply Qlt_0_neg_lt_not_r in E4.
      apply Qeq_by_elim in E4; trivial.
      rewrite E4, Qneg_0 in E2.
      apply Qeq_sym; trivial.
    - apply C0 in q as ?.
      unfold step in S0.
      destruct S0 as (D0 & V0 & A0 & A0' & NN0 & NN0' & S0).
      apply Qle_not_lt in NN0 as E3.
      apply Qle_lt_trans with (z:=c_v c') in NN0 as E4; trivial.
      apply Qeq_neg in E2.
      rewrite E2 in E4.
      apply Qlt_0_neg_lt_not_r in E4.
      apply Qeq_by_elim in E4; trivial.
    - unfold step in S0.
      destruct S0 as (D0 & V0 & S0).
      rewrite H, Qmult_0_l, Qplus_0_r in V0.
      apply Qeq_0_by_eq_neg in V0; trivial.
      rewrite V0, Qneg_0 in E2.
      apply Qeq_sym; trivial.
  }

  assert (c_a c == 0) as E4.
  {
    unfold step in S0.
    destruct S0 as (D0 & V0 & S0).
    rewrite E3 in E2, V0.
    apply Qeq_neg with (a:=c_v c') in E2.
    rewrite Qneg_0 in E2.
    rewrite E2, Qplus_0_l in V0.
    SearchAbout (_*_==0).
    apply Qmult_eq_0_l with (a:=c_a c) in PosT.
    apply Qeq_sym, PosT in V0; trivial.
  }

  assert (c_l c == c_l c') as E5.
  {
    unfold step in S0.
    intuition.
  }

  assert (c_lane c = c_lane c') as E6.
  {
    unfold step in S0.
    intuition.
  }

  assert (c_a c == c_a c') as E7.
  {
    apply Qeq_neg in E1.
    rewrite E1, E4, Qneg_0.
    reflexivity.
  }

  assert (c_v c == c_v c') as E8.
  {
    apply Qeq_neg in E2.
    rewrite E2, E3, Qneg_0.
    reflexivity.
  }

  unfold equ_car_st.
  intuition.
Qed.

(* 
Lemma multi_step_no_loop : forall (c c' c'' : car_st), step c c' -> multi step c' c'' -> step c'' c -> equ_car_st c c''.
Proof.
  intros * S0 MS S1.
  induction MS.
  - apply step_no_loop in S1; trivial.
  -
Qed. *)

(*
Lemma multi_step_no_loop : forall (c c' : car_st), multi step c c' -> multi step c' c -> c' = c.
Proof.
  intros * MS0 MS1.
  apply multi_no_reverse_driving in MS0 as E0.
  apply Qle_antisym in E0; [|apply multi_no_reverse_driving in MS1; trivial].

  

  induction MS0.
  - reflexivity.
  - apply multi_R in H as MS2.
    apply (multi_trans (car_st) (step) z x y) in MS1 as MS3; trivial.

    apply multi_no_reverse_driving in MS3 as E1.
    apply IHMS0 in MS3 as EQ0.
    rewrite <- EQ0 in H.
    clear MS0 MS2 MS3 IHMS0 EQ0 y.
    apply no_reverse_driving in H as E0.

    apply Qle_antisym in E0; [|apply multi_no_reverse_driving in MS1; trivial].
    clear H.

    induction MS1.
    * reflexivity.
    * apply no_reverse_driving in H as E1.
      apply multi_no_reverse_driving in MS1 as E2.
      rewrite <- E0 in E2.
      apply Qle_antisym in E1; trivial.
      

    
    unfold step in H.
    destruct H as (D & V & H).
    rewrite E0 in D.
    rewrite <- Qplus_assoc, Qplus_r_equ_sub_l, Qplus_neg, Qplus_opp_r in D.
    
    SearchAbout (_ == _ + _).


    induction MS1.
    * reflexivity.
    *

    assert (x = y \/ ~ x = y) as C by admit.
    destruct C as [C0 | C1].
    * rewrite C0; trivial.
    * induction MS1. { reflexivity. }
      apply multi_R in H0 as MS3.
        apply (multi_trans (car_st) (step) y x y0) in MS0; trivial.
        apply IHMS1 in H as EQ1; trivial.

    
    
Qed.
 *)


Lemma can_multi_dmin_step_const_acc_snd : forall  (c : car_st*car_st),
  (exists (c' : car_st*car_st), multi d_min_step c c' /\ const_acc (snd c) (snd c')).
Proof.
  intros *.

  exists c.
  split.
  - apply multi_refl.
  - unfold const_acc.
    intros * MS0 MS1.
Qed.

Lemma multi_d_min_step_alt_path_br_req : forall (c c' : car_st*car_st),
  multi d_min_step c c' ->
  (exists (d d' : car_st*car_st),
    multi d_min_step d d' /\
    non_acc_equ_state (rear c) (rear d) /\
    const_acc (rear d) (rear d') /\
    c_a (rear d) == a_br_req /\
    multi d_min_compare_step (c, d) (c', d')).
Proof.
  intros * MDStep0.
  pose (d:=(acc_choice_p_snd c a_br_req)).
  exists d.
  assert ((exists (d' : car_st*car_st), multi d_min_step d d')) as H by apply can_multi_dmin_step.
  destruct H as [d' MDStep1].
  exists d'.
  repeat split; trivial.

Qed.



Lemma multi_d_min_step_dist_bound2: forall (c1 c1' c2 c2' : car_st*car_st), 
  multi d_min_compare_step (c1, c2) (c1', c2') ->
  non_acc_equ_state (rear c1) (rear c2) -> d_min_compare_const_front (c1, c2) (c1', c2') ->
  const_acc (rear c2) (rear c2') -> c_a (rear c2) == a_br_req -> 
  d_min_brake_mode c1 c1' ->
  c_x (rear c1') - c_x (rear c1) <= c_x (rear c2') - c_x (rear c2).
Proof.
  intros * MDCStep EQR EQF1 EQF2 ConstAcc InitAcc BrakeMode.
Admitted.


Lemma d_min_safe_brake : forall (c c' c'' : car_st*car_st),
  d_min_step c c' ->
  multi d_min_step c' c'' ->
  d_min_brake_mode c' c'' ->
  max_stopping_dist (rear c) - min_stopping_dist (front c) < c_rear_x (front c') - c_x (rear c') ->
  0 < c_rear_x (front c'') - c_x (rear c'').
Proof.
  intros * DStep0 MDStep1 DBrake Dist0.
(*   apply acc_choice_p_snd in c' as d'; [|exact a_br_req]. *)

  
Admitted.


Lemma d_min_safe_multi_step : forall (c c' : car_st*car_st),
  (d_min_holds_p c) -> same_lane (fst c) (snd c)  -> multi d_min_step c c' -> collision_free_multi_dmin_step c c'.
Proof.
  intros * InitDMin L0 MDStep.
  unfold collision_free_multi_dmin_step.
  
  split.
  {
    now (apply d_min_init_no_collision).
  }

  split; trivial.
  intros * MDStep0 MDStep1 L2.

  assert (d_min_holds_p c'' \/ ~d_min_holds_p c'') as C.
  { 
    unfold d_min_holds_p, d_min_holds.
    admit.
  }
  destruct C.
  - split.
    {
      now (apply d_min_init_no_collision).
    }

    split.
    {
      intros.
      apply d_min_holds_ordering in InitDMin.
      unfold front,rear in *.
      apply Qlt_not_lt in InitDMin.
      contradiction.
    }
    intros.
    apply d_min_holds_ordering in H; trivial.

  - apply d_min_transition_invariant with (c':=c'') in InitDMin as Inv; trivial.
    destruct Inv as [i [i' (MDStepI0 & DStepI1 & MDStepI2 & DMinI1 & DMinI2)]].
    apply d_min_holds_response_dist with (c':=i') in DMinI1 as Dist0; trivial.

    apply d_min_safe_brake with (c'':=c'') in DStepI1 as Dist1; trivial.
    rewrite Qplus_neg, <- Qlt_minus_iff in Dist1.
    split.
    {
      unfold collision.
      unfold front,rear in *.
      intro G.
      destruct G as (L2' & [[E0 E1] | [E0 E1]]); clear L2'.
      - apply Qle_lt_trans with (z:=c_rear_x (fst c'')) in E1; trivial.
        apply car_rear_lt_false in E1.
        contradiction.
      - apply Qlt_le_trans with (z:=c_x (snd c'')) in Dist1; trivial.
        apply Qlt_irrefl in Dist1.
        contradiction.
    }

    split.
    {
      intros H0.
      apply d_min_holds_ordering in InitDMin.
      unfold front,rear in *.
      apply Qlt_not_lt in InitDMin.
      contradiction.
    }

    intros H0.
    SearchAbout (c_rear_x).
    apply car_order_rear_weakening in Dist1.
    unfold front, rear in *.
    assumption.
Qed.


End RoadContext.