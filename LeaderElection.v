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
  { rcount : nat
  ; max : nat
  ; has_sent : {ffun 'I_n -> bool}
  }.

Definition set_send_node (s : node_st) i : node_st :=
  {| rcount := s.(rcount)
   ; max := s.(max)
   ; has_sent := update s.(has_sent) i (fun _ => true)
  |}.

Definition node_recv (s : node_st) m :=
  {| rcount := s.(rcount).+1
   ; max := maxn s.(max) m
   ; has_sent := s.(has_sent)
  |}.

(* Definition node_recv (s : node_st)  *)

Record cprotocol_st :=
 { cqueues : {ffun 'I_n -> seq nat}
 ; cnode_sts : {ffun 'I_n -> node_st}
 }.

Definition set_send (s : cprotocol_st) (i j : 'I_n) : cprotocol_st :=
  {| cqueues := update s.(cqueues) j (fun pq => [:: val i & pq])
   ; cnode_sts := update s.(cnode_sts) i (fun pst => set_send_node pst j)
  |}.

Definition do_recv (s : cprotocol_st) m i :=
  {| cnode_sts := update s.(cnode_sts) i (fun pst => node_recv pst m)
   ; cqueues := update s.(cqueues) i (fun pq => rem m pq)
   |}.

Definition get_max (s : cprotocol_st) i :=
  (s.(cnode_sts) i).(max).

Inductive label := Eps | Decided of nat.

Definition get_label s i :=
  if (s.(cnode_sts) i).(rcount) < n
  then Eps
  else Decided (get_max s i).

Reserved Notation "s1 --[ l ]-->_c s2" (at level 30).

Inductive concrete_step : cprotocol_st -> label -> cprotocol_st -> Prop :=
  | Send :
    forall s1 i j,
      (s1.(cnode_sts) i).(has_sent) j = false ->
      let s2 := set_send s1 i j in
   (* ---------------------------- *)
      s1 --[Eps]-->_c s2

  | Recv :
    forall s1 i (m : 'I_n),
      (* (s1.(node_sts) i).(rcount).+1 < n -> *)
      val m \in s1.(cqueues) i ->
      let s2 := do_recv s1 i m in
   (* ---------------------------- *)
      s1 --[get_label s2 i]-->_c s2

  (* | Decide : *)
  (*   forall s1 i (m : 'I_n), *)
  (*     (s1.(node_sts) i).(rcount).+1 = n -> *)
  (*     val m \in s1.(queues) i -> *)
  (*     let s2 := do_recv s1 i m in *)
  (*  (* ---------------------------- *) *)
  (*     s1 --[Decided (get_max s2 i) ]--> s2 *)

where "s1 --[ l ]-->_c s2" := (concrete_step s1 l s2).

Inductive Phase := SendP of nat | RecvP of nat.

Record aprotocol_st :=
 { phase : Phase
 (* ; step_i : nat *)
 (* ; step_j : nat *)
 ; aqueues : {ffun 'I_n -> seq nat}
 ; anode_sts : {ffun 'I_n -> node_st}
 }.

Definition set_phase s p :=
  {| phase := p
   ; aqueues := s.(aqueues)
   ; anode_sts := s.(anode_sts)
   |}.

Definition phase_next p (hsent : {ffun 'I_n -> bool}):=
  match p with
  | SendP i =>
      if [forall i, hsent i == true] then
        if i < n
        then SendP i.+1
        else RecvP 0
      else SendP i
  | RecvP i => RecvP i.+1
  end.

Definition set_asend (s : aprotocol_st) (i j : 'I_n) : aprotocol_st :=
  {| phase := phase_next s.(phase) (s.(anode_sts) i).(has_sent)
   ; aqueues := update s.(aqueues) j (fun pq => [:: val i & pq])
   ; anode_sts := update s.(anode_sts) i (fun pst => set_send_node pst j)
  |}.

Reserved Notation "s1 --[ l ]-->_a s2" (at level 30).

Inductive abs_step : aprotocol_st -> label -> aprotocol_st -> Prop :=
  | A_Send :
    forall s1 (i : 'I_n) j,
      s1.(phase) = SendP i ->
      (s1.(anode_sts) i).(has_sent) j = false ->
      let s2 := set_asend s1 i j in
   (* ---------------------------- *)
      s1 --[Eps]-->_a s2

where "s1 --[ l ]-->_a s2" := (abs_step s1 l s2).
