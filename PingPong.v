From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Aux.

Definition update (T : finType) S (m : {ffun T -> S}) (x : T) (f : S -> S) : {ffun T -> S} :=
  [ffun i => if i == x then f (m i) else m i].

End Aux.

(*  Concrete State Nodes *)
Record c_node_st :=
{
    x : nat
;   ch : seq nat
}.

(* Initial node states *)
Definition init_ping := 
    {|  x := 0
    ;   ch := [:: 0]
    |}.

Definition init_pong := 
    {|  x := 0
    ;   ch := [::]
    |}.

(* Operations on nodes *)
Definition u_inc (s : c_node_st) : c_node_st := 
    {|  x := s.(x).+1
    ;   ch := s.(ch)
    |}.

Definition u_add (s : c_node_st) m : c_node_st := 
    {|  x := s.(x)
    ;   ch := [:: m & (s.(ch) ) ]
    |}.


Definition u_rem (s : c_node_st) m := 
    {|  x := m
    ;   ch := rem m s.(ch)
    |}.


(* Concrete States *)
Record c_st :=
    {   ping : c_node_st
    ;   pong : c_node_st
    }.

(* Initial Concrete States*)
Definition c_init : c_st :=
    {|  ping := init_ping
    ;   pong := init_pong
    |}.

(* Concrete State Operations *)
Definition do_ping (s : c_st) m := 
    {|  ping := u_inc (u_rem s.(ping) m)
    ;   pong := u_add s.(pong) m.+1
    |}.

Definition do_pong (s : c_st) m := 
    {|  ping := u_add s.(ping) m
    ;   pong := u_rem s.(pong) m
    |}.

(* Concrete Transition Relation *)
Inductive label := Eps | curVal of nat.

Reserved Notation "s1 --[ l ]-->_c s2" (at level 30).

Inductive c_step : c_st -> label -> c_st -> Prop := 
    | ping_step:
        forall s1 m,
        m \in s1.(ping).(ch) ->
        let s2 := do_ping s1 m in
    (* ----------------------- *)
        s1--[Eps]-->_c s2
    
    | pong_step:
        forall s1 m,
        m \in s1.(pong).(ch) ->
        let s2 := do_pong s1 m in
    (* ----------------------- *)
        s1--[curVal m]-->_c s2
where "s1 --[ l ]-->_c s2" := (c_step s1 l s2).

(* Abstract State Defn *)
Record a_st :=
    {   val : nat
    }.

(* Abstract Initial State *)

Definition a_init : a_st := 
    {|  val := 0
    |}.

(* Abstract Operations *)
Definition u_incVal (s : a_st) :=
    {|  val := s.(val).+1
    |}.

(* Abstract Transition Relation *)
Reserved Notation "s1 --[ l ]-->_a s2" (at level 30).

Inductive a_step : a_st -> label -> a_st -> Prop := 
    | abs_step:
        forall s1,
        let s2 := u_incVal s1  in
    (* ----------------------- *)
        s1--[Eps]-->_a s2

where "s1 --[ l ]-->_a s2" := (a_step s1 l s2).
