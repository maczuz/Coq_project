Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia. 
Require Import Lra.

(*Record graph := {
  V : Set;
  edges : V -> V -> bool
  }.
  
Require Import Coq.Vectors.Fin.
  
Definition ex : graph := {| V := t 3; edges := fun u => fun v => 
  match u , v with
  | F1, FS F1 | FS F1, F1 => true
  | _,_ => false
  end  |}. *)
  
Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.

Import ListNotations.
  
Inductive BoolPlus := Ptrue | Pfalse | Pbzdura.

Record graph := graph1 {
  vertex : list nat;
  edges : nat -> nat -> BoolPlus;
  dowod : forall (x : nat), (In x vertex) \/ (forall y : nat, edges x y = Pbzdura /\ edges y x = Pbzdura)
  }.
  

Fixpoint contains (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | f::ls => if Nat.eqb x f then true else contains x ls
  end.
  
Eval compute in contains 4 [ 1 ; 2; 3 ].


Fixpoint nodup (l : list nat) : list nat :=
    match l with
      | [] => []
      | x::xs => if contains x xs then nodup xs else x::(nodup xs)
    end.
    
Eval compute in nodup [1 ; 2; 1].
  
Definition degree (g : graph) (v : nat) : nat := length( filter (fun x => match x with | Ptrue => true | _ => false end) (map (edges g v) (nodup(vertex g)))).

Definition bipartite (g : graph) := exists (f : nat -> bool), forall ( u v : nat), (edges g u v = Ptrue) -> not (f u = f v).

Definition edges1 (x y : nat) : BoolPlus :=
  match x, y with
  | 1, 2 | 2, 3 | 2, 1 | 3, 2 => Ptrue
  | 1, 3 | 3, 1 => Pfalse
  | _, _ => Pbzdura
  end.
  
Theorem dowod1: forall (x : nat), In x [ 1; 2; 3 ] \/ (forall y, edges1 x y = Pbzdura /\ edges1 y x = Pbzdura).
Proof.
  intros.
  destruct x.
  right.
  unfold edges1.
  split.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  trivial.
  destruct x.
  left.
  unfold In.
  left.
  trivial.
  destruct x.
  left.
  unfold In.
  right.
  left.
  trivial. 
  destruct x.
  left.
  unfold In.
  right.
  right.
  left.
  trivial.
  right.
  split.
  unfold edges1.
  trivial.
  unfold edges1.
  destruct y.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  trivial.
Qed.
  

Definition ex1 := graph1 [ 1; 2; 3 ] edges1 dowod1.

Eval compute in degree ex1 2.

Theorem example_graph_is_bipartite : bipartite ex1.
Proof.
  unfold bipartite.
  exists (fun x => match x with | 1 | 3 => true | _ => false end).
  intros.
  destruct u.
  destruct v.
  discriminate.
  destruct v.
  lia.
  destruct v.
  discriminate.
  destruct v.
  lia.
  discriminate.
  destruct u.
  destruct v.
  lia.
  destruct v.
  discriminate.
  destruct v.
  lia.
  destruct v.
  discriminate.
  lia.
  destruct u.
  destruct v.
  discriminate.
  destruct v.
  lia.
  destruct v.
  discriminate.
  destruct v.
  lia.
  discriminate.
  destruct u.
  destruct v.
  lia.
  destruct v.
  discriminate.
  destruct v.
  lia.
  destruct v.
  discriminate.
  lia.
  destruct v.
  discriminate.
  destruct v.
  discriminate.
  destruct v.
  discriminate.
  destruct v.
  lia.
  discriminate.
Qed. 


Definition correctcol (g : graph) (f : nat -> nat) := forall (u v : nat), (edges g u v = Ptrue) -> f u <> f v.

Definition coloring1 (x : nat) : nat :=
  match x with
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | _ => 0
  end.

Theorem example_coloring_is_correct : correctcol ex1 coloring1.
Proof.
  unfold correctcol.
  intros.
  destruct v.
  destruct u.
  simpl.
  discriminate.
  destruct u.
  unfold not.
  discriminate.
  unfold not.
  destruct u.
  discriminate.
  destruct u.
  discriminate.
  simpl.
  discriminate.
  destruct u.
  destruct v.
  unfold not.
  discriminate.
  unfold not.
  discriminate.
  destruct u.
  destruct v.
  unfold not.
  discriminate.
  destruct v.
  simpl.
  trivial.
  destruct v.
  simpl.
  discriminate.
  simpl.
  lia.
  destruct u.
  destruct v.
  unfold not.
  discriminate.
  destruct v.
  simpl.
  discriminate.
  destruct v.
  simpl.
  lia.
  simpl.
  lia. 
  destruct u.
  destruct v.
  unfold not.
  discriminate.
  destruct v.
  simpl.
  trivial.
  destruct v.
  simpl.
  discriminate.
  simpl.
  lia. 
  destruct v.
  unfold not.
  discriminate.
  destruct v.
  simpl.
  trivial.
  destruct v.
  simpl.
  discriminate.
  simpl.
  discriminate.
Qed.

Theorem bipartite_is_bicoloring : forall (g : graph), bipartite g -> exists (col : nat -> nat), correctcol g col.

Proof.
  unfold bipartite in *.
  intros.
  destruct H.
  exists (fun v => match x v with | true => 1 | false => 2 end).
  unfold correctcol.
  intros.
  specialize (H u v).
  apply H in H0.
  unfold not in*.
  destruct (x u).
  destruct (x v).
  exfalso.
  apply H0.
  trivial.
  discriminate.
  destruct (x v).
  discriminate.
  exfalso.
  apply H0.
  trivial.
Qed.

Definition edges2 (x y : nat) : BoolPlus :=
  match x, y with
  | 1, 2 | 2, 3 | 3, 4 | 4, 1 | 2, 1 | 3, 2 | 4, 3 | 1, 4 => Ptrue
  | 1, 3 | 3, 1 | 2, 4 | 4, 2 => Pfalse
  | _, _ => Pbzdura
  end.
  
Theorem dowod2: forall (x : nat), In x [ 1; 2; 3; 4 ] \/ (forall y, edges2 x y = Pbzdura /\ edges2 y x = Pbzdura).
Proof.
  intros.
  destruct x.
  right.
  destruct y.
  split.
  trivial.
  trivial.
  split.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  simpl.
  trivial.
  destruct x.
  left.
  unfold In.
  left.
  trivial.
  destruct x.
  left.
  unfold In.
  right.
  left.
  trivial.
  destruct x.
  left.
  unfold In.
  right.
  right.
  left.
  trivial.
  destruct x.
  left.
  unfold In.
  right.
  right.
  right.
  left.
  trivial.
  right.
  destruct y.
  simpl.
  split.
  trivial.
  trivial.
  split.
  simpl.
  trivial.
  unfold edges2.
  destruct y.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  destruct y.
  trivial.
  trivial.
Qed.
  
Definition C_4 := graph1 [ 1; 2; 3; 4 ] edges2 dowod2.

Eval compute in C_4.

Theorem C_4_is_bipartite : bipartite C_4.
Proof.
  unfold bipartite.
  exists (fun x => match x with | 1 | 3 => true | _ => false end).
  intros.
  destruct u.
  destruct v.
  discriminate.
  destruct v.
  lia.
  destruct v.
  discriminate.
  destruct v.
  lia.
  discriminate.
  destruct u.
  destruct v.
  lia.
  destruct v.
  discriminate.
  destruct v.
  lia.
  destruct v.
  discriminate.
  lia.
  destruct u.
  destruct v.
  discriminate.
  destruct v.
  lia.
  destruct v.
  discriminate.
  destruct v.
  lia.
  destruct v.
  discriminate.
  destruct v.
  discriminate.
  discriminate.
  destruct u.
  destruct v.
  lia.
  destruct v.
  discriminate.
  destruct v.
  lia.
  destruct v.
  discriminate.
  lia.
  destruct v.
  destruct u.
  discriminate.
  discriminate.
  destruct v.
  discriminate.
  destruct v.
  destruct u.
  discriminate.
  discriminate.
  destruct v.
  lia.
  destruct v.
  destruct u.
  discriminate.
  discriminate.
  destruct u.
  discriminate.
  discriminate.
Qed. 

Theorem C_4_is_bicol : exists (col : nat -> nat), correctcol C_4 col.
Proof.
  apply (bipartite_is_bicoloring C_4).
  apply C_4_is_bipartite.
Qed.