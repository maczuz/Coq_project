Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia. 

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
    

Definition bipartite (g : graph) := exists (f : nat -> bool), forall ( u v : nat), In u (vertex g) /\ In v (vertex g) /\ (edges g u v = Ptrue) -> not (f u = f v).


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
  destruct H.
  destruct H0.
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
  lia.
  destruct v.
  discriminate.
  destruct v.
  lia.
  discriminate.
Qed.


