(*******************************************************************
 * Este archivo especifica el estado.
 *
 ******************************************************************)

Require Export Maps.

Section State.

(** Identificadores de OSs e Hypercalls *)

Parameter os_ident : Set.
Parameter os_ident_eq : forall oi1 oi2 : os_ident, {oi1 = oi2} + {oi1 <> oi2}.

Parameter Hyperv_call: Set.


(* Memoria y direcciones *)

(* Direcciones Virtuales. *)
Parameter vadd: Set.
Parameter vadd_eq : forall va1 va2 : vadd, {va1 = va2} + {va1 <> va2}.

(** Direcciones de Máquina. *)
Parameter madd :  Set.
Parameter madd_eq : forall ma1 ma2 : madd, {ma1 = ma2} + {ma1 <> ma2}.

(** Direcciones Físicas :
Los sitemas operativos utilizan este tipo de direcciones para ver regiones de memoriea
contigua. Estos no ven direcciones de máquina. *)
Parameter padd: Set.
Parameter padd_eq : forall pa1 pa2 : padd, {pa1 = pa2} + {pa1 <> pa2}.

(** Memory values. *)
Parameter value: Set.
Parameter value_eq:forall val1 val2 : value, {val1 = val2} + {val1 <> val2}.


(* Environment *)
Record context : Set :=
  Context
    {(** una dirección virtual es accesible, i.e. no está reserveda
         por el Hypervisor *)
       ctxt_vadd_accessible: vadd -> bool;
     (** guest Oss (Confiable/No Confiable) **)
       ctxt_oss : os_ident -> bool
    }.

Record os : Set :=
  OS {
    (* guest OS current page table (physical address) *)
    curr_page : padd;
    (* whether it has a hypercall pending to be resolved *)
    hcall : option Hyperv_call
  }.

Definition oss_map := os_ident -> os.

(* Execution modes *)

Inductive exec_mode :=
  | usr (* user mode *)
  | svc. (* supervisor mode *)

Inductive os_activity :=
  | running
  | waiting.

(* Memory mappings *)

Definition hypervisor_map := os_ident -> (padd -> madd).

Inductive content :=
  | RW (v: option value)
  | PT (va_to_ma : vadd -> madd)
  | Other.

Inductive page_owner :=
  | Hyp
  | Os (osi: os_ident)
  | No_Owner.

Record page : Set :=
  Page {
    page_content: content;
    page_owned_by : page_owner
  }.

Definition system_memory := madd -> page.

Record state : Set :=
  State {
    active_os : os_ident;
    aos_exec_mode : exec_mode;
    aos_activity : os_activity;
    oss : oss_map;
    hypervisor : hypervisor_map;
    memory : system_memory
  }.

End State.