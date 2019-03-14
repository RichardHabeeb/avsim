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
  c_ts : nat;
}.

Variables dt a_max a_min a_br_req : Q.

Hypothesis PosT : dt > 0.
Hypothesis BrakeReq : a_br_req < 0.
Hypothesis BrakeMax : a_min <= a_br_req.
Hypothesis AccMax : a_max > 0.
Hypothesis PosLen: forall c:car_st, 0 < c_l c.

Definition c_rear_x (c : car_st) := (c_x c) - (c_l c).

Definition same_lane (c1 : car_st) (c2 : car_st) := (c_lane c1 = c_lane c2).

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
  (c_l c == c_l c') /\
  (* Increase timestamp *)
  (c_ts c' = S (c_ts c)).


Definition collision (c1 : car_st) (c2 : car_st) :=
  (same_lane c1 c2) /\
  ((c_x c1 >= c_rear_x c2) /\ (c_x c1 <= c_x c2) \/
   (c_x c2 >= c_rear_x c1) /\ (c_x c2 <= c_x c1)).

Definition collision_free_step (c1 : car_st) (c1' : car_st) (c2 : car_st) (c2' : car_st) :=
  ~(collision c1 c2) /\ (same_lane c1 c2) /\
  (step c1 c1') /\ (step c2 c2') /\
  ~(collision c1' c2') /\
  (c_x c1 < c_x c2 -> c_x c1' < c_x c2') /\ (* Relative orderings must be the same, no instantaneous passing *)
  (c_x c2 < c_x c1 -> c_x c2' < c_x c1').


Definition non_acc_equ_state (c1 c2 : car_st) := 
  (c_x c1 == c_x c2) /\
  (c_v c1 == c_v c2) /\
  (c_l c1 == c_l c2) /\
  (c_lane c1 = c_lane c2) /\
  (c_ts c1 = c_ts c2).

Definition max_stopping_dist (c : car_st) := -((c_v c + a_max*dt)^2)/((2#1)*a_br_req).
Definition min_stopping_dist (c : car_st) := -((c_v c)^2)/((2#1)*a_min).

Definition d_min_holds (cf : car_st) (cr : car_st) :=
  (c_rear_x cf) > (c_x cr) /\ (* This is implied by the following but it's here for convenience *)
  (c_rear_x cf) - (c_x cr) > ((c_v cr)*dt + a_max*dt^2/(2#1)) /\
  (c_rear_x cf) - (c_x cr) > 
  (c_v cr)*dt + a_max*dt^2/(2#1) + max_stopping_dist cr - min_stopping_dist cf.

Definition const_acc (c c' : car_st) := (forall c'', multi step c c'' -> multi step c'' c' -> c_a c == c_a c'').


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
  rewrite H9.
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


Lemma d_min_holds_collision_free_step : forall (cf cf' cr cr' : car_st),
  d_min_holds cf cr -> same_lane cf cr -> step cf cf' -> step cr cr' -> collision_free_step cf cf' cr cr'.
Proof.
  intros * init_d_min lane stepf stepr.
  unfold collision_free_step.
  split.
  {
    unfold d_min_holds in init_d_min.
    unfold step in stepf.
    unfold step in stepr.
    unfold collision.
    intuition.
    + apply Qle_lt_trans with (x:=c_x cf) (y:=c_x cr) (z:=c_rear_x cf) in H29 as A0; trivial.
      assert (c_rear_x cf < c_x cf) as A1 by apply car_rear_lt.
      apply Qlt_not_lt in A1.
      contradiction.
    + apply Qlt_not_le in H0.
      contradiction.
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
      rewrite H22.
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


Lemma d_min_holds_response_dist : forall (cf cf' cr cr' : car_st),
  d_min_holds cf cr -> same_lane cf cr -> step cf cf' -> step cr cr' -> 
    (c_rear_x cf' - c_x cr' > (max_stopping_dist cr - min_stopping_dist cf)).
Proof.
  intros * init_d_min lane stepf stepr.
  unfold d_min_holds in init_d_min.
  apply no_reverse_driving_rear in stepf as fRearDiff.
  unfold step in stepf.
  unfold step in stepr.
  intuition.
  apply Qplus_l_lt_sub_l with (a:=c_x cr').
  rewrite H3.
  rewrite <- !Qplus_assoc.
  apply Qplus_l_lt_sub_l with (a:=c_x cr).
  rewrite !Qplus_neg, !Qplus_assoc.
  apply Qlt_r_plus_le_weak_l with (a:=c_rear_x cf); trivial.
  rewrite Qplus_comm with (y:=c_a cr * dt ^ 2 / (2 # 1)).
  rewrite <- !Qplus_assoc.
  apply Qlt_l_plus_le_weak_l with (a:=a_max * dt ^ 2 / (2 # 1)).
  - rewrite !Qplus_assoc, <- !Qplus_neg.
    rewrite Qplus_comm with (x:=a_max * dt ^ 2 / (2 # 1)).
    assumption.
  - rewrite !Qsquare, !Qdiv_mult_inv, !Qmult_assoc.
    repeat apply Qmult_le_compat_r; auto with qarith.
Qed.




End RoadContext.