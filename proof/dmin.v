Require Import QArith.
Require Import Qminmax.
Require Import List.

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

Lemma Qlt_neg_lt : forall a, 0 < a <-> -a < 0.
Proof.
  intros; split; intros.
  - apply Qopp_lt_compat in H.
    now(rewrite Qneg_0 in H).
  - apply Qopp_lt_compat in H.
    now(rewrite Qneg_0,Qopp_opp in H).
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


Lemma Qle_div_inj: forall a b c, 0 < c -> a <= b <-> a/c <= b/c.
Proof.
  intros * Hc.
  split; intros Heq.
  - rewrite <- Qmult_le_l with (z:=c); [rewrite Qmult_div_r; [rewrite Qmult_div_r|]|]; auto with qarith.
  - rewrite <- Qmult_le_l with (z:=c) in Heq; [rewrite Qmult_div_r in Heq; [rewrite Qmult_div_r in Heq|]|]; auto with qarith.
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
Ltac  plus_opp_simpl :=
  first [progress plus_minus | progress minus_plus]; rewrite ?Qplus_opp_l, ?Qplus_opp_r, ?Qplus_0_r, ?Qplus_0_l.







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

Inductive multi' {X : Type} (R : relation X) : relation X :=
  | multi_refl' : forall(x : X), multi' R x x
  | multi_step' : forall(x y z : X),
                    multi' R x y ->
                    R y z ->
                    multi' R x z.

Theorem multi_R' : forall(X : Type) (R : relation X) (x y : X),
    R x y -> (multi' R) x y.
Proof.
  intros X R x y H.
  apply multi_step' with x; trivial.
  apply multi_refl'.
Qed.

Theorem multi_trans' :
  forall(X : Type) (R : relation X) (x y z : X),
      multi' R x y ->
      multi' R y z ->
      multi' R x z.
Proof.
  intros X R x y z G H.
  induction H.
  - assumption.
  - apply multi_step' with y; trivial.
    apply IHmulti'. assumption.
Qed.


Theorem multi_multi' : forall (X:Type) (x y : X) (R :relation X),
  multi R x y <-> multi' R x y.
Proof.
  intros; split.
  - induction 1.
    * apply multi_refl'.
    * apply multi_R' in H.
      apply multi_trans' with y; trivial.
  - induction 1.
    * apply multi_refl.
    * apply multi_R in H0.
      apply multi_trans with y; trivial.
Qed.



(** ##############################################################################
DEFINITIONS 
################################################################################*)
Section RoadContext.


(*
  Kinematic State (of an object)
*)
Record k_st := {
  k_x : Q;
  k_v : Q;
  k_l : Q;
  k_lane : nat; (* TODO: generalize to lateral posision *)
}.


(* 
  Car State 
*)
Record car := {
  (* Instantaneous physical state of the car *)
  c_st : k_st;

  (*
    Acceleration decision making relation.
    This predicate will be true iff the car is
    following the rules of the road given an
    acceleration and an sensor observation.
  *)
  c_acc_ai : k_st -> option k_st -> Q -> Prop;
}.


(*
  Definitions of kinematic state equivalence
*)
Definition eq_k_st (k k' : k_st) :=
  (k_x k) == (k_x k') /\
  (k_v k) == (k_v k') /\
  (k_l k) == (k_l k') /\
  (k_lane k) = (k_lane k').
Lemma eq_k_st_refl k : eq_k_st k k.
Proof. unfold eq_k_st. intuition. Qed.
Lemma eq_k_st_sym k k' : eq_k_st k k' -> eq_k_st k' k.
Proof. unfold eq_k_st. intuition. Qed.
Lemma eq_k_st_trans k k' k'' : eq_k_st k k' -> eq_k_st k' k'' -> eq_k_st k k''.
Proof. 
  unfold eq_k_st.
  intros (Hx & Hv & Hl & Hln).
  rewrite Hx,Hv,Hl,Hln; trivial.
Qed.
Global Instance eq_k_st_equiv : Equivalence eq_k_st.
Proof.
  split; hnf.
  apply eq_k_st_refl.
  apply eq_k_st_sym.
  apply eq_k_st_trans.
Qed.
Definition eq_k_st_opt (a b : option k_st) := 
  match a,b with
  | Some a', Some b' => eq_k_st a' b'
  | Some _, None => False
  | None, Some _ => False
  | None, None => True
  end.
Global Instance some_k_st_morph : Proper(eq_k_st ==> eq_k_st_opt) (Some).
Proof. hnf; intros. unfold eq_k_st_opt; trivial. Qed.


(*
  Definition of car state equivalence
*)
Definition eq_car_st (c c' : car) := eq_k_st (c_st c) (c_st c') /\ (c_acc_ai c = c_acc_ai c'). 
Lemma eq_car_st_refl c : eq_car_st c c.
Proof. unfold eq_car_st,eq_k_st. intuition. Qed.
Lemma eq_car_st_sym c c' : eq_car_st c c' -> eq_car_st c' c.
Proof. unfold eq_car_st,eq_k_st. intuition. Qed.
Lemma eq_car_st_trans c c' c'' : eq_car_st c c' -> eq_car_st c' c'' -> eq_car_st c c''.
Proof. 
  intros * (K0 & A0) (K1 & A1).
  unfold eq_car_st; split.
  - apply eq_k_st_trans with (k':=c_st c'); trivial.
  - rewrite A0,A1; trivial.
Qed.
Global Instance eq_car_st_equiv : Equivalence eq_car_st.
Proof.
  split; hnf.
  apply eq_car_st_refl.
  apply eq_car_st_sym.
  apply eq_car_st_trans.
Qed.



(* 
  Definition of car state pair equivalence
*)
Definition eq_car_st_p (c c' : car*car) := 
  (eq_car_st (fst c) (fst c')) /\ (eq_car_st (snd c) (snd c')).
Lemma eq_car_st_p_refl c : eq_car_st_p c c.
Proof. unfold eq_car_st_p. intuition. Qed.
Lemma eq_car_st_p_sym c c' : eq_car_st_p c c' -> eq_car_st_p c' c.
Proof. unfold eq_car_st_p. intuition. Qed.
Lemma eq_car_st_p_trans c c' c'' : eq_car_st_p c c' -> eq_car_st_p c' c'' -> eq_car_st_p c c''.
Proof.
  unfold eq_car_st_p. intuition.
  - now (rewrite H1).
  - now (rewrite H2).
Qed.
Global Instance eq_car_st_p_equiv : Equivalence eq_car_st_p.
Proof.
  split; hnf.
  apply eq_car_st_p_refl.
  apply eq_car_st_p_sym.
  apply eq_car_st_p_trans.
Qed.


(*
  Scenario Constants
*)
Variables dt a_max a_min a_br_req : Q.
Hypothesis PosT : dt > 0.
Hypothesis BrakeReq : a_br_req < 0.
Hypothesis BrakeMax : a_min <= a_br_req.
Hypothesis AccMax : a_max > 0.
Hypothesis PosLen: forall k:k_st, 0 < k_l k.


(*
  Record morphisms and helpers
*)
Global Instance k_x_morph : Proper (eq_k_st ==> Qeq) (k_x).
Proof. hnf; intros. unfold eq_k_st in *. intuition. Qed.
Global Instance k_v_morph : Proper (eq_k_st ==> Qeq) (k_v).
Proof. hnf; intros. unfold eq_k_st in *. intuition. Qed.
Global Instance k_l_morph : Proper (eq_k_st ==> Qeq) (k_l).
Proof. hnf; intros. unfold eq_k_st in *. intuition. Qed.
Global Instance k_lane_morph : Proper (eq_k_st ==> eq_nat) (k_lane).
Proof. hnf; intros. unfold eq_k_st in *. intuition. Qed.

Global Instance c_st_morph : Proper (eq_car_st ==> eq_k_st) (c_st).
Proof. hnf; intros. unfold eq_car_st in *. intuition. Qed.

Definition c_x c:= (k_x (c_st c)).
Definition c_v c:= (k_v (c_st c)).
Definition c_l c:= (k_l (c_st c)).

Global Instance c_x_morph : Proper (eq_car_st ==> Qeq) (c_x).
Proof. hnf; intros. unfold c_x. now (rewrite H). Qed.
Global Instance c_v_morph : Proper (eq_car_st ==> Qeq) (c_v).
Proof. hnf; intros. unfold c_v. now (rewrite H). Qed.
Global Instance c_l_morph : Proper (eq_car_st ==> Qeq) (c_l).
Proof. hnf; intros. unfold c_l. now (rewrite H). Qed.

(*
  Car bumper position, and morphism
*)
Definition k_rear_x (k : k_st) := (k_x k) - (k_l k).
Global Instance k_rear_x_morph : Proper (eq_k_st ==> Qeq) (k_rear_x).
Proof. hnf; intros. unfold k_rear_x. rewrite H. reflexivity. Qed.

Definition c_rear_x (c : car) := k_rear_x (c_st c).
Global Instance c_rear_x_morph : Proper (eq_car_st ==> Qeq) (c_rear_x).
Proof. hnf; intros. unfold c_rear_x. rewrite H. reflexivity. Qed.


(*
  Lane equivalence
*)
Definition same_lane (c1 c2 : car) := (k_lane (c_st c1) = k_lane (c_st c2)).
Lemma same_lane_refl c : same_lane c c.
Proof. unfold same_lane. intuition. Qed.
Lemma same_lane_sym c c' : same_lane c c' -> same_lane c' c.
Proof. unfold same_lane. intuition. Qed.
Lemma same_lane_trans c c' c'' : same_lane c c' -> same_lane c' c'' -> same_lane c c''.
Proof. intros. unfold same_lane in *. intuition. Qed.
Global Instance same_lane_equiv : Equivalence same_lane.
Proof.
  split; hnf.
  apply same_lane_refl.
  apply same_lane_sym.
  apply same_lane_trans.
Qed.
Lemma same_lane_dec : forall (c1 c2 : car), {same_lane c1 c2} + {~same_lane c1 c2}.
Proof. intros.  unfold same_lane. apply Nat.eq_dec. Qed.


(*
  Given an observed car in front, this relation is true if c can move to c' according to newtonian kinematics
  and according to a car's decision making function. This step function assumes that acceleration can be
  adjusted instantaneously. Future models should take into account jerk to make this more accurate.
*)
Definition step (a:Q) (obs : option k_st) (c c' : car) :=
  (* Kinematics *)
  c_x c' == (c_x c) + (c_v c)*dt + (a*dt^2)/(2#1) /\
  c_v c' == (c_v c) + a*dt /\
  (* Decision making function/monitor. Is this "a" valid? *)
  ((c_acc_ai c) (c_st c) obs a) /\
  (* Constant length *)
  c_l c == c_l c' /\
  (* Single lane (for now) *)
  (same_lane c c').



(*
  Helper definitions for the minimum distance calculations.
*)
Definition max_stopping_dist (k : k_st) := -((k_v k + a_max*dt)^2)/((2#1)*a_br_req).
Definition min_stopping_dist (k : k_st) := -((k_v k)^2)/((2#1)*a_min).
Definition d_min (kr kf : k_st) :=
  (k_rear_x kf) > (k_x kr) /\
  (k_rear_x kf) - (k_x kr) > ((k_v kr)*dt + a_max*dt^2/(2#1)) /\
  (k_rear_x kf) - (k_x kr) > 
    (k_v kr)*dt + a_max*dt^2/(2#1) + 
    max_stopping_dist kr - min_stopping_dist kf. (*TODO ADD CASE FOR STOPPING*)
Lemma d_min_dec : forall kr kf, {d_min kr kf} + {~ d_min kr kf}.
Proof.
  intros.
  unfold d_min.
  destruct (Qlt_le_dec 
    (k_x kr)
    (k_rear_x kf))
    as [LT0|LE0];
  destruct (Qlt_le_dec 
    (k_v kr * dt + a_max * dt ^ 2 / (2 # 1))
    (k_rear_x kf - k_x kr ))
    as [LT1|LE1];
  destruct (Qlt_le_dec 
    (k_v kr * dt + a_max * dt ^ 2 / (2 # 1) +
       max_stopping_dist kr - min_stopping_dist kf)
    (k_rear_x kf - k_x kr ))
    as [LT2|LE2];
  try apply Qle_not_lt in LE0;
  try apply Qle_not_lt in LE1;
  try apply Qle_not_lt in LE2;
  intuition.
Qed.
Definition d_min_p (p :car*car) := d_min (c_st (snd p)) (c_st (fst p)).
Lemma d_min_p_dec : forall p, {d_min_p p} + {~d_min_p p}.
Proof. intros. unfold d_min_p. apply d_min_dec. Qed.

Definition will_stop (k : k_st) (a:Q) := 
  ((k_v k + a*dt < 0) \/
  ((k_v k)*dt + (a*dt^2)/(2#1) < 0)).
Lemma will_stop_dec : forall k a, {will_stop k a} + {~will_stop k a}.
Proof.
  intros.
  unfold will_stop.
  destruct (Qlt_le_dec (k_v k + a * dt) 0) as [LT0|LE0];
    destruct (Qlt_le_dec (k_v k * dt + a * dt ^ 2 / (2 # 1)) 0) as [LT1|LE1];
    try apply Qle_not_lt in LE0;
    try apply Qle_not_lt in LE1;
    intuition.
Qed.

(*
  Decision making function based on a minimum distance calculation and assumptions about rules of the road
*)
Definition d_min_rules (kr : k_st) (kf : option k_st) (a : Q) :=
  (* No reverse driving *)
  0 <= (k_v kr) /\
  0 <= (k_v kr) + a*dt /\
  0 <= (k_v kr)*dt + (a*dt^2)/(2#1) /\

  (* Bounded acceleration *)
  a_min <= a <= a_max /\

  (* Minimum distance violation *)
  match kf, (will_stop_dec kr a_br_req) with
    | Some kf', left _  => (~ d_min kr kf') -> (a == (k_v kr)/dt) (* Stop without reversing *)
    | Some kf', right _ => (~ d_min kr kf') -> (a <= a_br_req) (* Apply minimum braking *)
    | None, _ => True (* No observed car in front *)
  end.
Global Instance d_min_rules_morph : Proper (eq_k_st ==> eq_k_st_opt ==> Qeq ==> iff) (d_min_rules).
Proof.
  hnf; intros * (X & V & L & Ln); hnf; intros * E0; hnf; intros * E1.
  unfold d_min_rules,d_min,min_stopping_dist,max_stopping_dist,eq_k_st_opt in *.
  destruct x0, y0,(will_stop_dec x a_br_req),(will_stop_dec y a_br_req);
  rewrite ?X,?V,?E0,?E1;
  try reflexivity;
  unfold will_stop in *;
  try rewrite ?V in w; try rewrite ?V in n;
  contradiction.
Qed.

(*
  Pairwise step following d_min_rules
*)
Definition d_min_step (c c' : car*car) := forall a', (exists a,
  (c_acc_ai (fst c)) = d_min_rules /\
  (c_acc_ai (snd c)) = d_min_rules /\
  (c_acc_ai (fst c')) = d_min_rules /\
  (c_acc_ai (snd c')) = d_min_rules /\
  (step a (Some (c_st (fst c))) (snd c) (snd c')) /\
  (step a' None (fst c) (fst c'))).


(*
  Instantaneous Collision
*)
Definition collision (c1 c2 : car) :=
  (same_lane c1 c2) /\
  ((c_rear_x c2 <= c_x c1 /\ c_x c1 <= c_x c2) \/
   (c_rear_x c1 <= c_x c2 /\ c_x c2 <= c_x c1)).

(*
  Definition of a safe step
*)
Definition collision_free_d_min_step (c c' : car*car) :=
  d_min_step c c' /\
  (* No initial collision *)
  (~ collision (fst c) (snd c)) /\
  (* No final collision *)
  (~ collision (fst c') (snd c')) /\ 
  (* Relative orderings must be the same, no instantaneous passing *)
  (c_x (fst c) < c_x (snd c) -> c_x (fst c') < c_x (snd c')) /\ 
  (c_x (snd c) < c_x (fst c) -> c_x (snd c') < c_x (fst c')).

(*
  Brake mode step
*)
Definition brake_mode_step (c c' : car*car) :=
  d_min_step c c' /\ ~(d_min_p c).

Definition collision_free_brake_mode_step (c c' : car*car) :=
  collision_free_d_min_step c c' /\ ~ d_min_p c.



Global Instance d_min_step_morph : Proper (eq_car_st_p ==> eq_car_st_p ==> iff) (d_min_step).
Proof.
  hnf; intros * EQ0; hnf; intros * EQ1.
  assert (eq_car_st_p x y) as EQ0' by auto.
  assert (eq_car_st_p x0 y0) as EQ1' by auto.
  unfold eq_car_st_p,eq_car_st,d_min_step,step in EQ0,EQ1|-*.
  destruct EQ0 as (((XF0 & VF0 & LF0 & NF0) & AF0) & ((XS0 & VS0 & LS0 & NS0) & AS0)).
  destruct EQ1 as (((XF1 & VF1 & LF1 & NF1) & AF1) & ((XS1 & VS1 & LS1 & NS1) & AS1)).
  unfold c_x,c_v,c_l,same_lane in *.
  split; intros; destruct H with a';
  exists x1;
  [ rewrite <-!XS0,<-!VS0,<-!LS0,<-!NS0,<-AS0;
    rewrite <-!XF0,<-!VF0,<-!LF0,<-!NF0,<-AF0;
    rewrite <-!XS1,<-!VS1,<-!LS1,<-!NS1,<-AS1;
    rewrite <-!XF1,<-!VF1,<-!LF1,<-!NF1,<-AF1
    |
    rewrite !XS0,!VS0,!LS0,!NS0,AS0;
    rewrite !XF0,!VF0,!LF0,!NF0,AF0;
    rewrite !XS1,!VS1,!LS1,!NS1,AS1;
    rewrite !XF1,!VF1,!LF1,!NF1,AF1
  ];
  destruct H0 as (D0 & D1 & D2 & D3 & H0);
  rewrite D0,D1;
  rewrite D0,D1 in H0;
  destruct EQ0' as [EQF0 EQS0];
  destruct EQ1' as [EQF1 EQS1];
  unfold eq_car_st_p in *;
  intuition.
  - now (rewrite <-EQS0,<-EQF0).
  - unfold d_min_rules in *.
    intuition; rewrite <-EQF0; trivial.
  - now (rewrite EQS0,EQF0).
  - unfold d_min_rules in *.
    intuition; rewrite EQF0; trivial.
Qed.



Definition init_conditions (p : car*car) := d_min_p p.
Lemma init_conditions_dec : forall p, {init_conditions p} + {~init_conditions p}.
Proof.
  intros.
  unfold init_conditions.
  apply d_min_p_dec.
Qed.


Definition d_min_invariant (p p' : car*car) :=
  ((max_stopping_dist (c_st (snd p)) - min_stopping_dist (c_st (fst p))) < (c_rear_x (fst p') - c_x (snd p'))).

(** ##############################################################################
MOTION THEOREMS 
################################################################################*)


Lemma k_rear_lt : forall (k : k_st), k_rear_x k < k_x k.
Proof.
  intros.
  unfold k_rear_x.
  apply Qplus_lt_l with (z:=-k_x k).
  rewrite !Qplus_neg,Qplus_comm,!Qplus_assoc,Qplus_opp_l,Qplus_opp_r,Qplus_0_l.
  assert (0 < k_l k) as H by apply PosLen.
  now (apply Qlt_neg_lt).
Qed.

Lemma c_rear_lt : forall c : car, c_rear_x c < c_x c.
Proof. intros. unfold c_rear_x, c_x. apply k_rear_lt. Qed.

Lemma no_reverse_driving : forall (c c' : car) (a : Q) (obs : option k_st),
  (step a obs c c') -> (c_acc_ai c) = d_min_rules -> (c_x c <= c_x c').
Proof.
  intros * S AI.
  destruct S as (X & V & S).
  rewrite AI in S.
  unfold d_min_rules in S.
  rewrite X.
  apply Qle_minus_iff.
  rewrite <-!Qplus_assoc.
  plus_minus.
  rewrite Qplus_opp_r,Qplus_0_r.
  unfold c_v.
  intuition.
Qed.

Lemma d_min_step_no_reverse : forall (p p' : car*car),
  d_min_step p p' -> (c_x (snd p) <= c_x (snd p') /\ c_x (fst p) <= c_x (fst p')).
Proof.
  intros * H.
  unfold d_min_step in *.
  assert(Q) as a'; auto.
  destruct H with a' as [a (A0 & A1 & A2 & A3 & S0 & S1)]; clear H.
  apply no_reverse_driving in S0; trivial.
  apply no_reverse_driving in S1; trivial.
  auto.
Qed.


Lemma multi_collision_free_d_min_step_weak : forall (p p': car*car),
  multi collision_free_d_min_step p p' -> multi d_min_step p p'.
Proof.
  intros * S.
  induction S.
  - apply multi_refl.
  - destruct H.
    apply multi_step with (z0:=z) in H; trivial.
Qed.

Lemma multi_collision_free_brake_mode_step_weak1 : forall (p p' : car*car),
  multi collision_free_brake_mode_step p p' -> multi brake_mode_step p p'.
Proof.
  intros * S.
  induction S.
  - apply multi_refl.
  - destruct H as ((? & ?) & ?).
    apply multi_step with y; unfold brake_mode_step; auto.
Qed.

Lemma multi_collision_free_brake_mode_step_weak2 : forall (p p' : car*car),
  multi collision_free_brake_mode_step p p' -> multi collision_free_d_min_step p p'.
Proof.
  intros * S.
  induction S.
  - apply multi_refl.
  - destruct H.
    apply multi_step with y; auto.
Qed.


Lemma d_min_single_safety : forall (p p' : car*car),
  d_min_p p -> d_min_step p p' -> collision_free_d_min_step p p'.
Proof.
Admitted.

Lemma d_min_transition_existence : forall (p p' : car*car),
  d_min_p p -> ~ d_min_p p' -> multi collision_free_d_min_step p p' ->
  (exists i i', 
    multi collision_free_d_min_step p i /\
    collision_free_d_min_step i i' /\
    d_min_p i /\
    multi collision_free_brake_mode_step i' p'). (* TODO: need to be brake mode steps? *)
Proof.
Admitted.

Lemma d_min_transition_invariant : forall (p p' : car*car),
  d_min_p p -> collision_free_d_min_step p p' -> ~ d_min_p p' -> d_min_invariant p p'.
Proof.
Admitted.


Lemma d_min_safe_brake : forall (p p' p'' : car*car),
  collision_free_d_min_step p p' ->  multi brake_mode_step p' p'' ->
  d_min_invariant p p' -> c_x (snd p'') < c_rear_x (fst p'').
Proof.
  intros * DS MS I.
Admitted.


Lemma d_min_no_collision : forall (p : car*car), d_min_p p -> ~collision (fst p) (snd p).
Proof.
  unfold not.
  intros * H C.
  unfold d_min_p,d_min,collision,c_rear_x,c_x in *.
  destruct H as (H0 & H1 & H2).
  destruct C as (L &  [[E0 E1] | [E0 E1]]).
  - apply Qlt_trans with (z:=k_x (c_st (fst p))) in H0.
    * apply Qlt_not_le in H0. contradiction.
    * apply k_rear_lt.
  - apply Qlt_not_le in H0. contradiction. 
Qed.

Lemma d_min_intermediate_collision_free : forall (p p' : car*car),
  d_min_p p -> multi collision_free_d_min_step p p' -> ~collision (fst p') (snd p').
Proof.
  intros * Init S.
  rewrite multi_multi' in S.
  induction S.
  - now (apply d_min_no_collision).
  - unfold collision_free_d_min_step in H.
    intuition.
Qed.

Lemma disjoint_no_collision : forall p : car*car, 
  c_x (snd p) < c_rear_x (fst p) -> ~ collision (fst p) (snd p).
Proof. 
  intros.
  unfold collision,not.
  intros (Ln & [[E0 E1] | [E0 E1]]).
  - apply Qle_lt_trans with (z:=c_rear_x (fst p)) in E1; trivial.
    apply Qlt_not_lt in E1.
    assert (c_rear_x (fst p) < c_x (fst p)) by apply c_rear_lt.
    contradiction.
  - apply Qlt_le_trans with (z:=c_x (snd p)) in H; trivial.
    assert (~ c_x (snd p) < c_x (snd p)) by apply Qlt_irrefl.
    contradiction.
Qed.



Theorem safety : forall (p p' p'' : car*car),
  init_conditions p -> multi collision_free_d_min_step p p' -> d_min_step p' p'' -> collision_free_d_min_step p' p''.
Proof.
  intros * Init MS0 DS1.
  
  (* Either d_min holds or it doesn't at p' *)
  destruct (d_min_p_dec p') as [C0|C0].
  - now (apply d_min_single_safety with (p':=p'') in C0).
  - unfold init_conditions in *.
    (* There exists a point when d_min started to not hold *)
    apply d_min_transition_existence with (p':=p') in Init as T0; trivial.
    destruct T0 as [i [i' (MSI0 & SI & DI & MSI1)]].

    (* The distance between the two cars at the transition point is > d_min. *)
    apply d_min_transition_invariant with (p':=i') in SI as Inv; trivial.
    * assert (multi brake_mode_step i' p'') as MSI2.
      {
        apply multi_collision_free_brake_mode_step_weak1 in MSI1.
        apply multi_trans with (y:=p'); trivial.
        assert (brake_mode_step p' p'').
        {
          unfold brake_mode_step. intuition.
        }
        now (apply multi_R).
      }
      (* The hard lemma, show that there is still space if a car has been braking *)
      apply d_min_safe_brake with(p'':=p'') in SI as Dp'; trivial.
      unfold collision_free_d_min_step.
      
      split; auto.
      split. (* The cars are not colliding at p' *)
      {
        assert (multi collision_free_d_min_step i p') as MSI3.
        {
          apply multi_collision_free_brake_mode_step_weak2 in MSI1.
          apply multi_step with (z:=p') in SI; trivial.
        }
        apply d_min_intermediate_collision_free with (p':=p') in DI as ?; trivial.
      }
      
      split. (* The cars are not colliding at p'' *)
      {
        apply disjoint_no_collision; trivial.
      }

      split.
      {
        intros C1.
        apply d_min_step_no_reverse in DS1 as [E0 E1].

    * 

    
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
  intros * S.
  unfold step in *.
  unfold c_rear_x.
  destruct S as (X & V & V' & Ln & L & S). 
  rewrite !Qplus_neg,L.
  apply Qplus_le_l.
  auto.
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

Lemma const_acc_step_weak : forall (c c' : car_st), const_acc_step c c' -> step c c'.
Proof.
  intros.
  unfold const_acc_step in *.
  intuition.
Qed.


Lemma step_dist: forall (c c' : car_st), 
  wont_stop c -> step c c' -> ~ c_a c == 0 -> (c_x c' - c_x c) == (c_v c' ^ 2 - c_v c ^ 2) / ((2#1)*c_a c).
Proof.
  intros * WS S Anz.
  unfold step in S.
  destruct S as (XX & V0 & V0' & Ln & L & C0 & C1).
  apply C0 in WS as (H & H1).

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
  multi const_acc_forward_step c c' -> ~ c_a c == 0 ->
  (c_x c' - c_x c) == (c_v c' ^ 2 - c_v c ^ 2) / ((2#1)*c_a c).
Proof.
  intros * MSfull Anz.
  induction MSfull.
  - rewrite !Qplus_neg.
    rewrite !Qplus_opp_r.
    rewrite Qdiv_mult_inv.
    rewrite Qmult_0_l.
    reflexivity.
  - destruct H as [[S A] WS].
    apply step_dist in S as D0; trivial.
    apply multi_R in S as HMS.
    rewrite A in Anz.
    apply IHMSfull in Anz as G1.
    + apply Qeq_sym in D0 as D1.
      rewrite <- Qplus_l_equ_sub_r in D1.
      rewrite <- D1 in G1.
      apply Qeq_sym in G1.
      rewrite <- Qplus_l_equ_sub_r in G1.
      rewrite !Qplus_assoc in G1.
      rewrite <- A in G1; trivial.
      rewrite !Qplus_neg in G1.
      rewrite <- Qdiv_sum2_dist_r in G1.
      rewrite !Qplus_assoc in G1.
      rewrite <- Qplus_assoc with (y:=- c_v y ^ 2) in G1.
      rewrite Qplus_opp_l in G1.
      rewrite Qplus_0_r in G1.
      rewrite Qplus_l_equ_sub_r in G1.
      apply Qeq_sym in G1.
      assumption.
Qed.

Lemma wont_stop_dec : forall c, wont_stop c \/ ~wont_stop c.
Proof.
  intros.
  unfold wont_stop.
  rewrite <- Qopp_involutive with (q:= c_a c * dt), <- Qle_minus_iff.
  rewrite <- Qplus_le_r with (x:=c_x c) (z:=-c_x c), !Qplus_assoc, !Qplus_opp_l, !Qplus_0_l.
  rewrite <- Qopp_involutive with (q:= c_a c * (dt * dt) / (2 # 1)), <- Qle_minus_iff.
  destruct (Qlt_le_dec (c_v c) (-(c_a c *dt))) as [H|H].
  - apply Qlt_not_le in H.
    intuition.
  - destruct (Qlt_le_dec (c_v c * dt) (-(c_a c * (dt * dt) / (2 # 1)))) as [H0|H0]; intuition.
    apply Qlt_not_le in H0.
    intuition.
Qed.

Lemma faster_car_wont_stop : forall (c1 c2 : car_st),
  (c_v c2 <= c_v c1) -> (c_a c2 <= c_a c1 ) -> wont_stop c2 -> wont_stop c1.
Proof.
  intros * VFast AFast [B0 B1].
  unfold wont_stop in *.
  split.
  - apply Qmult_le_r with (z:=dt) in AFast; auto with qarith.
    apply Qplus_le_compat with (z:=c_v c2) (t:=c_v c1) in AFast; trivial.
    rewrite Qplus_comm, Qplus_comm with (y:=c_v c1) in AFast.
    apply Qle_trans with (z:=c_v c1 + c_a c1 * dt) in B0; trivial.
  - apply Qplus_le_l with (z:=-c_x c1).
    rewrite <-!Qplus_assoc.
    plus_opp_simpl.
    apply Qplus_le_r with (z:=-c_x c2) in B1.
    rewrite !Qplus_assoc, !Qplus_opp_l, Qplus_0_l in B1.
    apply Qmult_le_r with (z:=dt*dt/(2#1)) in AFast.
    + apply Qplus_le_compat with (z:=c_v c2 * dt) (t:=c_v c1 * dt) in AFast.
      * rewrite Qplus_comm, Qplus_comm with (y:=c_v c1 * dt) in AFast.
        rewrite !Qdiv_mult_inv, <-!Qmult_assoc in *.
        apply Qle_trans with (z:=c_v c1 * dt + c_a c1 * (dt * (dt * / (2 # 1)))) in B1; trivial.
      * apply Qmult_le_r; auto with qarith.
    + apply Qmult_0_lt; auto with qarith.
      rewrite <-Qsquare.
      apply dt_squared_pos.
Qed.

(*
Lemma faster_car_bigger_step : forall (c1 c1' c2 c2' : car_st),
  (c_v c1 >= c_v c2) -> (c_a c1 >= c_a c2) ->
  (step c1 c1') -> (step c2 c2') ->
  (c_x c1' - c_x c1 >= c_x c2' - c_x c2).
Proof.
  intros * VFast AFast S1 S2.
  unfold step in *.

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

  destruct (wont_stop_dec c1) as [WS1|WS1]; 
    destruct (wont_stop_dec c2) as [WS2|WS2];
    apply S1 in WS1 as H1;
    apply S2 in WS2 as H2;
    destruct H1 as [X1 V1];
    destruct H2 as [X2 V2];
    rewrite X1,X2.
  - rewrite !Qplus_neg, <-!Qplus_assoc.
    plus_opp_simpl.
    rewrite !Qsquare, !Qmult_assoc.
    apply Qplus_le_compat; assumption.
  - apply faster_car_wont_stop in VFast as WS3; trivial.
    rewrite !Qplus_neg, Qplus_opp_r, <-!Qplus_assoc.
    plus_opp_simpl.
    
    
Qed. *)

(* 
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

Lemma step_no_loop : forall (c c' : car_st), step c c' -> step c' c -> eq_car_st c c'.
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

  unfold eq_car_st.
  intuition.
Qed.
*)

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


Lemma d_min_holds_collision_free_step : forall (c c' : car_st*car_st),
  d_min_holds_p c -> same_lane_p c -> d_min_step c c' -> collision_free_step_p c c'.
Proof.
  intros * I Ln S.
  unfold collision_free_step.
  split.
  {
    apply d_min_holds_no_inst_collision; trivial.
  }

  unfold d_min_holds in I.
  destruct S as (B0 & B1 & B2 & SF & SR).

  split; trivial.
  split; trivial.
  split; trivial.

  assert (0 <= c_v (rear c) * dt) as A0.
  {
    unfold step in SR.
    apply Qmult_le_0_compat; intuition.
  }

  assert (0 <= dt^2) as A1 by apply dt_squared_nonneg.
  assert (0 <= a_max*dt^2/(2#1)) as A2 by apply a_max_term_pos.

  assert (c_rear_x (front c) <= c_rear_x (front c')) as A3.
  {
    destruct SF as (XF & VF & VF' & LnF & LF & WSF & WSF').
    unfold c_rear_x.
    rewrite !Qplus_neg.
    rewrite LF.
    rewrite Qplus_le_l; trivial.
  }

  apply Qplus_le_compat with (t:=a_max*dt^2/(2#1)) (z:=0) in A0; trivial.
  rewrite Qplus_0_l in A0.

  assert (c_rear_x (front c') - c_x (rear c') > 0) as A4.
  {
    destruct SF as (XF & VF & VF' & LnF & LF & WSF & WSF').
    destruct SR as (XR & VR & VR' & LnR & LR & WSR & WSR').
    unfold min_max_bound_p in B1,B2.
    destruct (wont_stop_dec (front c)) as [C0|C0];
    destruct (wont_stop_dec (rear c)) as [C1|C1];
    try apply WSF in C0 as (KX0 & KV0);
    try apply WSF' in C0 as (KX0 & KV0);
    try apply WSR in C1 as (KX1 & KV1);
    try apply WSR' in C1 as (KX1 & KV1);
    destruct I as (I0 & I1 & I2); clear WSR WSF WSR' WSF'.
    - rewrite KX1, !Qplus_neg.
      apply Qlt_minus_iff with (q:=c_rear_x (front c')).
      rewrite <- Qplus_assoc.
      apply Qplus_l_lt_sub_l.
      apply Qlt_r_sub_le_weak_l with (a:=c_rear_x (front c)); trivial.
      apply Qlt_l_plus_le_weak_r with (b:=a_max * dt ^ 2 / (2 # 1)); trivial.
      apply Qmult_le_compat_r; auto with qarith.
      apply Qmult_le_compat_r; intuition.
    - rewrite Qplus_neg, KX1.
      apply Qlt_minus_iff with (p:=c_x (rear c)).
      apply Qlt_le_trans with (y:=c_rear_x (front c)); trivial.
    - rewrite KX1, !Qplus_neg.
      apply Qlt_minus_iff with (q:=c_rear_x (front c')).
      rewrite <- Qplus_assoc.
      apply Qplus_l_lt_sub_l.
      unfold c_rear_x in *.
      rewrite KX0, <-LF.
      apply Qle_lt_trans with (y:=c_v (rear c) * dt + a_max * dt ^ 2 / (2 # 1)); trivial.
      apply Qplus_le_r.
      apply Qmult_le_r; auto with qarith.
      apply Qmult_le_r.
      * apply dt_squared_pos.
      * unfold rear.
        intuition. 
    - unfold c_rear_x in *.
      rewrite KX0,KX1,<-LF, Qplus_neg.
      apply Qlt_minus_iff with (p:=c_x(rear c)); trivial.
  }

  apply Qlt_minus_iff in A4.
  apply car_order_rear_weakening in A4 as A5.
  apply Qlt_not_le in A4 as A6.
  apply Qlt_not_le in A5 as A7.

  split.
  {
    unfold collision.
    intuition.
  }
  split; trivial.
  intros C.
  unfold d_min_holds_p,d_min_holds,rear,front in *.
  destruct I as [I0 I].
  apply car_order_rear_weakening in I0.
  apply Qlt_not_lt in I0.
  contradiction.
Qed.


(*
Lemma d_min_holds_response_dist : forall (c c' : car_st*car_st),
  d_min_holds_p c -> d_min_step c c' -> 
    (c_rear_x (front c') - c_x (rear c') > (max_stopping_dist (rear c) - min_stopping_dist (front c))).
Proof.
  intros * InitDMin DStep.
  unfold d_min_holds_p in InitDMin.
  unfold d_min_holds in InitDMin.
  unfold d_min_step in DStep.
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
*)








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


Lemma d_min_transition_invariant : forall (c c' : car_st*car_st),
  (d_min_holds_p c) -> same_lane (fst c) (snd c) -> multi d_min_step c c' -> ~(d_min_holds_p c') ->
  (exists (i i' : car_st*car_st),
    multi d_min_step c i /\
    d_min_holds_p i /\
    d_min_step i i' /\
    multi d_min_false_step i' c').
Proof.
Admitted.





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


(* 
Lemma can_step : forall (c: car_st), 
  wont_stop c -> (exists c' : car_st, step c c').
Proof.
  intros.
  unfold step.
  exists (Build_car_st
    (c_x c + c_v c * dt + c_a c * dt ^ 2 / (2 # 1))
    (c_v c + c_a c * dt)
    (c_a c)
    (c_l c)
    (c_lane c)).
  unfold same_lane.
  unfold wont_stop in H.
  simpl.
  intuition.
Qed.

Lemma can_const_acc_step : forall (c: car_st), 
  state_within_bounds c -> (exists c' : car_st, const_acc_step c c').
Proof.
  intros.
  unfold const_acc_step.
  exists (Build_car_st
    (c_x c + c_v c * dt + c_a c * dt ^ 2 / (2 # 1))
    (c_v c + c_a c * dt)
    (c_a c)
    (c_l c)
    (c_lane c)).
  unfold step, same_lane.
  unfold state_within_bounds in H.
  simpl.
  intuition.
Qed.

Lemma can_d_min_step : forall  (c : car_st*car_st),
  scenario_within_bounds c ->
  (exists (c' : car_st*car_st), d_min_step c c').
Proof.
  intros * B.
  unfold scenario_within_bounds in B.
  destruct B as [FB [SB B]].
  apply can_step in FB.
  apply can_step in SB.
  destruct FB as [fc' Sf].
  destruct SB as [sc' Ss].
  pose (c':=(fc',sc')).
  exists c'.
  unfold d_min_step.
  split; trivial.
  split; auto.
Qed.

Lemma step_within_bounds : forall (c c' : car_st), step c c' -> state_within_bounds c.
Proof.
  intros * S.
  unfold state_within_bounds,step in *.
  intuition.
  - now (rewrite H1 in H5).
  - now (rewrite H in H7).
Qed.

Lemma d_min_step_within_bounds : forall (c c' : car_st*car_st), d_min_step c c' -> scenario_within_bounds c.
Proof.
  intros * S.
  unfold scenario_within_bounds, d_min_step in *.
  destruct S as (B & SF & SS).
  apply step_within_bounds in SF.
  apply step_within_bounds in SS.
  auto.
Qed. *)

(* Lemma acc_choice_within_bounds : forall (c : car_st*car_st) (a:Q),
  scenario_within_bounds c ->
  a_min <= a <= a_max ->
  scenario_within_bounds (acc_choice_p_snd c a).
Proof.
  intros * Bc.
  unfold scenario_within_bounds in *.
  destruct Bc as (Bfc & Bsc & Bc).
  split.
  {
    unfold acc_choice_p_snd.
    auto.
  }
  split.
  {
    unfold acc_choice_p_snd, state_within_bounds in *.
    simpl.
    intuition.
  }
Qed.

Lemma can_choice_const_acc_step : forall (),
  (acc_choice_p_snd c a) 
  ->  state_within_bounds c -> (exists c' : car_st, const_acc_step c c'). *)

(* 
Lemma can_d_min_step_const_acc_choice_rear : forall  (p p' : car_st*car_st),
  scenario_within_bounds p -> 
  (exists (c c' : car_st), 
    non_acc_equ_state c (rear p) /\
    d_min_step_const_acc_rear (c, front p) (c', front p')).
Proof.
  intros * B.
  unfold scenario_within_bounds in B.
  destruct B as [FB [SB B]].
  pose (c:=(acc_choice_p_snd p a_br_req)).  
  assert (scenario_within_bounds c) as SB'.
  {
    unfold scenario_within_bounds.
    subst c.
    simpl.
    split; trivial.
    split.
    {
      clear FB.
      unfold state_within_bounds in *.
      simpl.
      destruct SB as ([BAmin BAmax] & Bv1 & Bv2 & Bx).
      intuition.
      - apply Qlt_le_weak.
        apply Qlt_trans with (z:=a_max) in BrakeReq; trivial.
      - assert (0 <= c_v (snd p) + a_min * dt) as HH by admit.

(*         apply Qle_trans with (z:=c_v (snd p) + a_ * dt) in HH; trivial. *)
        apply Qle_trans with (z:=c_v (snd p) + a_br_req * dt) in HH; trivial.
        apply Qplus_le_r.
        apply Qmult_le_r; auto.

    
  }
  pose (F:=can_const_acc_step (rear c)).
  apply can_step in FB.
  apply can_const_acc_step in SB.
  destruct FB as [fc' Sf].
  destruct SB as [sc' Ss].
  pose (c':=(fc',sc')).
  exists c'.
  unfold d_min_step_const_acc_rear; auto.
Qed.


Lemma multi_d_min_step_alt_path_br_req : forall (c c' : car_st*car_st),
  multi d_min_step c c' ->
  (exists (d d' : car_st*car_st),
    multi d_min_step_const_acc_rear d d' /\
    non_acc_equ_state (rear c) (rear d) /\
    c_a (rear d) == a_br_req /\
    multi scene_compare_step (c, d) (c', d')).
Proof.
  intros * MDStep0.
  pose (d:=(acc_choice_p_snd c a_br_req)).
  exists d.
  assert ((exists (d' : car_st*car_st), multi d_min_step_const_acc_rear d d')) as H by apply can_d_min_step_const_acc_rear.
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
Qed. *)


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


Lemma d_min_step_weak_fst : forall (c c' : car_st*car_st),
  d_min_step c c' -> step (fst c) (fst c').
Proof.
  intros * DStep.
  unfold d_min_step in DStep.
  intuition.
Qed.

Lemma d_min_step_weak_snd : forall (c c' : car_st*car_st),
  d_min_step c c' -> step (snd c) (snd c').
Proof.
  intros * DStep.
  unfold d_min_step in DStep.
  intuition.
Qed.


Lemma multi_d_min_step_weak_fst : forall (c c' : car_st*car_st),
  multi d_min_step c c' -> multi step (fst c) (fst c').
Proof.
  intros * MDStep.
  induction MDStep.
  - apply multi_refl.
  - apply d_min_step_weak_fst in H.
    apply multi_R in H.
    apply multi_trans with (y:=(fst y)); trivial.
Qed.

Lemma multi_d_min_step_weak_snd : forall (c c' : car_st*car_st),
  multi d_min_step c c' -> multi step (snd c) (snd c').
Proof.
  intros * MDStep.
  induction MDStep.
  - apply multi_refl.
  - apply d_min_step_weak_snd in H.
    apply multi_R in H.
    apply multi_trans with (y:=(snd y)); trivial.
Qed.


Lemma multi_d_min_step_collision_free_weak : forall (c c' : car_st*car_st),
  multi d_min_step_collision_free c c' -> multi d_min_step c c'.
Proof.
  intros * MS.
  induction MS.
  - apply multi_refl.
  - destruct H as (DS &? ).
    apply multi_step with (z0:=z) in DS; trivial.
Qed.


Lemma d_min_safe_same_lane : forall (c c' : car_st*car_st),
  same_lane (fst c) (snd c) -> multi d_min_step_collision_free c c' -> same_lane (fst c') (snd c').
Proof.
  intros * Ln0 MS.
  apply multi_d_min_step_collision_free_weak in MS.
  apply multi_d_min_step_weak_fst in MS as F.
  apply multi_d_min_step_weak_snd in MS as S.
  apply multi_step_same_lane in F.
  apply multi_step_same_lane in S.
  now (rewrite <-S,<-F).
Qed.


Lemma d_min_collision_free_multi_final : forall (c c' : car_st*car_st),
  (d_min_holds_p c) -> same_lane (fst c) (snd c)  -> multi d_min_step_collision_free c c' -> ~collision (fst c') (snd c').
Proof.
Admitted.

(* 
Lemma d_min_transition_invariant : forall (c c' : car_st*car_st),
  (d_min_holds_p c) -> same_lane (fst c) (snd c) -> multi d_min_step c c' -> ~(d_min_holds_p c') ->
  (exists (i i' : car_st*car_st),
    multi d_min_step c i /\
    d_min_holds_p i /\
    d_min_step i i' /\
    multi d_min_false_step i' c').
Proof. *)


Theorem d_min_safe_multi_step : forall (c c' c'' : car_st*car_st),
  (d_min_holds_p c) -> same_lane (fst c) (snd c)  -> multi d_min_step_collision_free c c' -> d_min_step c' c'' -> collision_free_step_p c' c''.
Proof.
  intros * I Ln MS0 S1.
  unfold collision_free_step_p, collision_free_step.

  split.
  { apply d_min_collision_free_multi_final with (c:=c); trivial. }

  split.
  { apply d_min_safe_same_lane with (c':=c') in Ln; trivial. }

  split.
  { apply d_min_step_weak_fst in S1; trivial. }

  split.
  { apply d_min_step_weak_snd in S1; trivial. }


  assert (d_min_holds_p c' \/ ~d_min_holds_p c') as C.
  { 
    unfold d_min_holds_p, d_min_holds.
    admit.
  }
  destruct C.
  - destruct S1 as (B & SF & SS).

  split.
  {



End RoadContext.
