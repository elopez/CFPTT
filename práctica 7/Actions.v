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
  (exists ma : madd, va_mapped_to_ma s va ma /\
  is_RW (page_content (memory s ma))).

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
  let curr_hcall := hcall (oss s curr_os) in
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

Definition valid_state_3 (s: state) :=
  let curr_os := active_os s in
  let trusted := ctxt_oss machine curr_os = true in
  let hyp_running := aos_activity s = waiting in
  (trusted \/ hyp_running) -> aos_exec_mode s = svc.

Definition valid_state_5 (s: state) :=
  forall (os: os_ident) (pa: padd),
  let hyp_pa_to_ma := hypervisor s os in
  let ma_owner := fun ma => page_owned_by (memory s ma) in
  ma_owner (hyp_pa_to_ma pa) = Os os /\
  forall (pa': padd), hyp_pa_to_ma pa = hyp_pa_to_ma pa' -> pa = pa'.

Definition valid_state_6 (s: state) :=
  forall (page: page),
  match page with
    | Page (PT vm) (Os owner) =>
        let va_owner := fun va => page_owned_by (memory s (vm va)) in
        let accessible := ctxt_vadd_accessible machine in
        forall (va: vadd),
          (accessible va = true /\ va_owner va = Os owner) \/
          (accessible va = false /\ va_owner va = Hyp)
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
      (exists (pg: page), pg = memory s ma /\ page_owned_by pg = Os (active_os s))).
Proof.
  (* let's simplify the proof a bit *)
  intros.
  inversion_clear H.
  inversion_clear H1.
  inversion_clear H3.
  destruct H4 as [x [H3 H4]].
  exists x.
  split; auto.
  exists (memory s x).
  split; auto.
  (* pose the valid state hypothesis into something useful *)
  destruct H0 as [V3 [V5 V6]].
  pose (V5 (active_os s) (curr_page (oss s (active_os s)))) as V5i.
  pose (V6 (memory s (hypervisor s (active_os s) (curr_page (oss s (active_os s)))))) as V6i.
  destruct V5i as [V5i_a V5i_b].
  (* prove the rest *)
  unfold va_mapped_to_ma in H3.
  destruct (memory s (hypervisor s (active_os s) (curr_page (oss s (active_os s))))).
  destruct page_content, page_owned_by; try inversion H3; try inversion V5i_a.
  inversion H3.
  pose (V6i va) as V6i_va.
  destruct V6i_va.
    * rewrite H6 in H7.
      destruct H7.
      assumption.
    * destruct H7.
      unfold os_accessible in H.
      rewrite H in H7.
      discriminate.
Qed.

End Actions.
