(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Require Export State.

Section Actions.

Inductive Action :=
  | read : vadd -> Action
  | write : vadd -> value -> Action
  | chmod : Action
.

Variable machine: context.
Definition os_accessible va := ctxt_vadd_accessible machine va = true.

(** READ **)
Definition pre_read (s: state) (va: vadd) :=
  os_accessible va /\
  aos_activity s = running /\
  (exists (ma : madd) (p : page), va_mapped_to_ma s va ma /\
  memory s ma = Some p /\ is_RW (page_content p)).

Definition post_read (s: state) (va: vadd) (s': state) := s = s'.

(** WRITE **)
Definition pre_write (s: state) (va: vadd) (v: value) := pre_read s va.

Definition post_write (s: state) (va: vadd) (v: value) (s': state) :=
  exists ma: madd, va_mapped_to_ma s va ma /\
  let new_page := Page (RW (Some v)) (Os (active_os s)) in
  let new_mem := update (memory s) ma new_page in
  mutate_memory s new_mem = s'.

(** CHMOD **)
Definition pre_chmod (s: state) :=
  aos_activity s = waiting /\
  let curr_os := active_os s in
  exists (ossmap: os), oss s curr_os = Some ossmap /\
  let curr_hcall := hcall ossmap in
  curr_hcall = None.

Definition post_chmod (s: state) (s': state) :=
  let curr_os := active_os s in
  let s_trusted := mutate_state s svc running in
  let s_untrusted := mutate_state s usr running in
  (ctxt_oss machine curr_os = true /\ s' = s_trusted) \/
  (ctxt_oss machine curr_os = false /\ s' = s_untrusted).

(* Pre and Post *)

Definition Pre (s: state) (a: Action) :=
  match a with
    | read va    => pre_read s va
    | write va v => pre_write s va v
    | chmod      => pre_chmod s
  end.

Definition Post (s: state) (a: Action) (s': state) :=
  match a with
    | read va    => post_read s va s'
    | write va v => post_write s va v s'
    | chmod      => post_chmod s s'
  end.

(* if the hypervisor or a trusted OS is running the processor
 * must be in supervisor mode *)
Definition valid_state_3 (s: state) :=
  let curr_os := active_os s in
  let trusted := ctxt_oss machine curr_os = true in
  let hyp_running := aos_activity s = waiting in
  (trusted \/ hyp_running) -> aos_exec_mode s = svc.

(* the hypervisor maps an OS physical address to a machine
 * address owned by that same OS. This mapping is also injective *)
Definition valid_state_5 (s: state) :=
  forall (os: os_ident) (pa: padd) (m: padd -> option madd) (p: page) (ma: madd),
  (hypervisor s os = Some m /\ m pa = Some ma /\ memory s ma = Some p) ->
    (page_owned_by p = Os os /\
    forall (pa': padd),
      m pa <> None /\ m pa' <> None /\ m pa = m pa' -> pa = pa').

(* all page tables of an OS o map accessible virtual addresses
 * to pages owned by o and not accessible ones to pages owned by
 * the hypervisor *)
Definition valid_state_6 (s: state) :=
  forall (pt: page),
  match pt with
    | Page (PT vm) (Os owner) =>
        let accessible := ctxt_vadd_accessible machine in
        forall (va: vadd), exists (ma: madd) (p: page),
          vm va = Some ma /\ memory s ma = Some p /\
          ((accessible va = true /\ page_owned_by p = Os owner) \/
          (accessible va = false /\ page_owned_by p = Hyp))
    | _ => True
  end.

Definition valid_state (s: state) :=
  valid_state_3 s /\ valid_state_5 s /\ valid_state_6 s.

Inductive one_step_execution (s s': state) (a: Action) :=
  step : valid_state s -> Pre s a -> Post s a s' -> one_step_execution s s' a.

Theorem execution_preserves_valid_state (a: Action) (s s': state) :
   valid_state_3 s -> one_step_execution s s' a -> valid_state_3 s'.
Proof.
  unfold valid_state_3.
  case a; intros.
    * inversion_clear H0.
      inversion H4.
      rewrite <- H0 in *.
      exact (H H1).
    * inversion_clear H0.
      inversion_clear H4.
      inversion_clear H0.
      inversion H5.
      unfold mutate_memory in H0.
      rewrite <- H0 in H1.
      exact (H H1).
    * inversion_clear H0.
      inversion_clear H4.
      + destruct H0.
        rewrite -> H4.
        reflexivity.
      + inversion_clear H3.
        destruct H0.
        rewrite -> H3 in H1.
        simpl in H1.
        elim H1; intros.
          - rewrite H0 in H6.
            discriminate.
          - discriminate.
Qed.


Lemma Read_isolation (s s': state) (va: vadd) :
  one_step_execution s s' (read va) ->
    (exists (ma: madd), va_mapped_to_ma s va ma /\
      (exists (pg: page), Some pg = memory s ma /\ page_owned_by pg = Os (active_os s))).
Proof.
  (* let's simplify the proof a bit *)
  intros.
  inversion_clear H.
  inversion_clear H1.
  destruct H3 as (running & pre_ma & pre_pg & pre_mapped & pre_ma_page & pre_rw).
  exists pre_ma.
  split; auto.
  exists pre_pg.
  split; auto.

  (* pose the valid state hypothesis into something useful *)
  destruct H0 as [V3 [V5 V6]].
  destruct pre_mapped as (os & pm & ma & pg & vm & _ & A1 & A2 & A3 & A4 & A5).
  pose (V5 (active_os s) (curr_page os) pm pg ma) as V5i.
  pose (V6 pg) as V6i.
  elim V5i; intros; auto.

  (* prove the rest *)
  destruct pg, page_content, page_owned_by; try inversion A4; try inversion H0.
  destruct (V6i va).
  destruct H3 as (B0 & B1 & B2 & B3).
  elim B3; intros;
    rewrite -> H4, -> A5 in B1;
    injection B1; intros;
    rewrite <- H6, -> pre_ma_page in B2;
    injection B2; intros.
    * rewrite <- H7, -> H5, -> H in H3.
      destruct H3; auto.
    * rewrite -> H in H3.
      destruct H3; discriminate.
Qed.

End Actions.
