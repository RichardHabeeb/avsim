Require Import List Setoid ZArith.
Import ListNotations.


Section GraphSearch.

Inductive vertex (T : Type) := {
	v_id : Z;
	v_data : T;
	neighbors : list (vertex T);
}.


Definition eq_vertex (T : Type) (v1 v2 : vertex T) :=
	(v_id T v1) = (v_id T v2) /\
	(v_data T v1) = (v_data T v2) /\
	(neighbors T v1) = (neighbors T v2).

Lemma eq_vertex_refl (T : Type) (v : vertex T) : eq_vertex T v v.
	Proof. unfold eq_vertex. auto. Qed.

Lemma eq_vertex_sym (T : Type) (v1 v2 :vertex T) : eq_vertex T v1 v2 -> eq_vertex T v2 v1.
	Proof. unfold eq_vertex. intuition. Qed.

Lemma eq_vertex_trans  (T : Type) (v1 v2 v3 : vertex T) : 
	eq_vertex T v1 v2 -> eq_vertex T v2 v3 -> eq_vertex T v1 v3.
	Proof.
	unfold eq_vertex in *.
	intros (I & V & N) ?.
	now (rewrite I; rewrite V; rewrite N).
	Qed.

Global Instance eq_vertex_equiv : forall (T: Type), Equivalence (eq_vertex T).
	Proof. intros. split; hnf; intros.
	- apply eq_vertex_refl.
	- apply eq_vertex_sym; trivial.
	- apply eq_vertex_trans with y; trivial.
	Qed.

	


Definition current_best_path (T : Type) (open : list (vertex T)) (best :) :=
	match open with
	| [] => None
	| h :: r => Some (fold_left best r)
	end.

Definition astar (T : Type) (orig dest : vertex T) (path : list (vertex T)) :=
	

