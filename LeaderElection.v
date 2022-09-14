From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Aux.

Definition update (T : finType) S (m : {ffun T -> S}) (x : T) (f : S -> S) : {ffun T -> S} :=
  [ffun i => if i == x then f (m i) else m i].

End Aux.

Variable (n : nat).

(* state per node *)
Record node_st :=
  { count : nat
  ; max : nat
  ; has_sent : {ffun 'I_n -> bool}
  }.

Definition set_send_node (s : node_st) i : node_st :=
  {| count := s.(count)
   ; max := s.(max)
   ; has_sent := update s.(has_sent) i (fun _ => true)
  |}.

Definition node_recv (s : node_st) m :=
  {| count := s.(count).+1
   ; max := maxn s.(max) m
   ; has_sent := s.(has_sent)
  |}.

(* Definition node_recv (s : node_st)  *)

Record protocol_st :=
 { queues : {ffun 'I_n -> seq nat}
 ; node_sts : {ffun 'I_n -> node_st}
 }.

Definition set_send (s : protocol_st) i j : protocol_st :=
  {| queues := s.(queues)
   ; node_sts := update s.(node_sts) i (fun pst => set_send_node pst j)
  |}.

Definition set_queue (s : protocol_st) i j :=
  {| node_sts := s.(node_sts)
   ; queues := update s.(queues) j (fun pq => [:: i & pq])
  |}.

Definition do_recv (s : protocol_st) m i :=
  {| node_sts := update s.(node_sts) i (fun pst => node_recv pst m)
   ; queues := update s.(queues) i (fun pq => rem m pq)
   |}.

Inductive label := Eps | Decide of nat.

Reserved Notation "s1 --[ l ]--> s2" (at level 30).

Inductive concrete_step : protocol_st -> label -> protocol_st -> Prop :=
  | Send :
    forall s1 i j,
      (s1.(node_sts) i).(has_sent) j = false ->
      let s2 := set_send s1 i j in
      let s2 := set_queue s2 i j in
   (* ---------------------------- *)
      s1 --[Eps]--> s2

  | Recv :
    forall s1 i (m : 'I_n),
      val m \in s1.(queues) i ->
      let s2 := do_recv s1 i m in
   (* ---------------------------- *)
      s1 --[Eps]--> s2

where "s1 --[ l ]--> s2" := (concrete_step s1 l s2).

