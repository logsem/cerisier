From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel proofmode.
From cap_machine Require Import macros hash_cap.

Class SecureOutsourcedCompute := {
    soc_addr : Addr;
  }.

Section soc_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    `{reservedaddresses : ReservedAddresses}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context {SOC : SecureOutsourcedCompute}.

  (* --------------------------------- *)
  (* --------- SOC *ENCLAVE* --------- *)
  (* --------------------------------- *)

  Definition soc_enclave_instrs : list instr :=
    [
      (* get signing sealing key *)
      Mov r_t1 PC;
      Lea r_t1 (-1)%Z;
      Load r_t1 r_t1;
      GetB r_t2 r_t1;
      GetA r_t3 r_t1;
      Sub r_t2 r_t2 r_t3;
      Lea r_t1 r_t2;
      Load r_t1 r_t1;
      GetE r_t3 r_t1;
      Sub r_t2 r_t3 1;
      Subseg r_t1 r_t2 r_t3;

      (* store the result (42) in a O-permission capability and sign it *)
      Mov r_t2 PC;
      GetA r_t3 r_t2;
      Sub r_t3 42 r_t3;
      Lea r_t2 r_t3;
      Restrict r_t2 (encodePerm O);
      Lea r_t1 1;
      Seal r_t2 r_t1 r_t2;

      (* share the signed value and the unsealing key to the adversary *)
      Restrict r_t1 (encodeSealPerms (false, true)); (* restrict r1 U *)
      Jmp r_t0
    ].
  Definition soc_enclave_code : list Word :=
    encodeInstrsW soc_enclave_instrs.

  Definition soc_enclave_lcode : list LWord :=
    encodeInstrsLW soc_enclave_instrs.

  Definition soc_enclave_code_len : Z :=
    Eval cbv in length soc_enclave_code.

  Definition hash_soc_enclave : Z :=
    hash_concat (hash soc_addr) (hash soc_enclave_code).


  (* ---------------------------------- *)
  (* ----------- SOC *MAIN* ----------- *)
  (* ---------------------------------- *)

  Definition soc_main_code_init0 (main callback data : Z) : list LWord :=
    (* main: *)
    encodeInstrsLW [
        Mov r_t1 PC;      (* rt1 := (RWX, main, main_end, main) *)

        (* Create callback sentry *)
        Lea r_t1 (callback - main)%Z;       (* rt1 := (RWX, main, main_end, callback) *)
        Restrict r_t1 (encodePerm E);       (* rt1 := (E, main, main_end, callback) *)

        (* Jump to adversary *)
        Jmp r_t0
      ].

  (* Expect PC := (RWX, main, main_end, callback) *)
  Definition soc_main_code_callback0
    (callback fails : Z)
    (hash_enclave : Z)
    (assert_lt_offset : Z)
    : list LWord :=
      (* callback: *)
      encodeInstrsLW [
        (* until the end, r3 contains the capability that bails out if something is wrong *)
        Mov r_t3 PC ;                 (* r_t3 :=  (RX, main, main_end, callback) *)
        Mov r_t4 r_t3 ;               (* r_t4 :=  (RX, main, main_end, callback) *)
        Lea r_t3 (fails-callback)%Z;  (* r_t3 :=  (RX, main, main_end, fails) *)

        (* sanity check: w_res is a sealed capability *)
        GetOType r_t2 r_t0;
        Sub r_t2 r_t2 (-1)%Z;
        Mov r_t5 PC ;
        Lea r_t5 4 ;
        Jnz r_t5 r_t2;
        Jmp r_t3;

        (*  attestation *)
        GetOType r_t2 r_t0;
        EStoreId r_t4 r_t2;
        (* check otype(w_res) against identity of the enclave *)
        Sub r_t4 r_t4 hash_enclave;
        Jnz r_t3 r_t4;

        (* get returned value and assert it to be 42 *)
        UnSeal r_t1 r_t1 r_t0;
        Mov r_t0 r_t5;
        GetA r_t4 r_t1;
        Mov r_t5 42%Z;
        Mov r_t1 r_t3%Z;
        Lea r_t1 1;
        Load r_t1 r_t1
      ]
      ++ assert_reg_instrs assert_lt_offset r_t1
      ++ encodeInstrsLW [Mov r_t0 0 ; Mov r_t3 0 ; Halt]
      ++ (* fails: *) encodeInstrsLW [Fail].

  Definition soc_main_init_len : Z :=
    Eval cbv in (length (soc_main_code_init0 0%Z 0%Z 0%Z)).

  Definition soc_main_callback_len : Z :=
    Eval cbv in (length (soc_main_code_callback0 0%Z 0%Z 0%Z 0%Z)).

  Definition soc_main_code (assert_lt_offset : Z) : list LWord :=
    let init     := 0%Z in
    let callback := soc_main_init_len in
    let data     := (soc_main_init_len + soc_main_callback_len)%Z in
    let fails    := (data - 1)%Z in
    (soc_main_code_init0 init callback data) ++
    (soc_main_code_callback0 callback fails hash_soc_enclave assert_lt_offset).

  Definition soc_main_code_len : Z :=
    Eval cbv in soc_main_init_len + soc_main_callback_len.

  Definition soc_main_data_len : Z := 2.
  Definition soc_main_len :=
    Eval cbv in (soc_main_code_len + soc_main_data_len)%Z.


  (* Sealed predicate for SOC enclave *)

  Program Definition f42 : Addr := (finz.FinZ 42 eq_refl eq_refl).
  Definition sealed_42 : LWord → iProp Σ :=
    λ w, (∃ b e v, ⌜w = LCap O b e f42 v⌝)%I.
  Definition sealed_42_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_42 w%I.

  Instance sealed_42_persistent w : Persistent (sealed_42 w).
  Proof. apply _. Qed.

  Definition seal_pred_42 τ := seal_pred τ sealed_42.
  Definition valid_sealed_cap w τ := valid_sealed w τ sealed_42.
  Lemma sealed_42_interp lw : sealed_42 lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed". iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
  Qed.

  (* SOC Custom Predicates *)
  Definition soc_enclave_pred : CustomEnclave :=
    @MkCustomEnclave Σ
      soc_enclave_code
      soc_addr
      (λ w, False%I)
      sealed_42.

  Definition soc_enclaves_map : custom_enclaves_map :=
   {[hash_soc_enclave := soc_enclave_pred]}.

  Lemma wf_soc_enclaves_map :
    custom_enclaves_map_wf soc_enclaves_map.
  Proof.
    rewrite /custom_enclaves_map_wf /soc_enclaves_map.
    split.
    - by rewrite map_Forall_singleton /hash_soc_enclave /=.
    - rewrite map_Forall_singleton; cbn.
      rewrite /encodeInstrW.
      apply Forall_forall.
      intros w Hw.
      repeat (rewrite elem_of_cons in Hw ; destruct Hw as [-> | Hw]; first done).
      by rewrite elem_of_nil in Hw.
  Qed.

  Definition contract_soc_enclaves_map :=
    MkCustomEnclavesMap soc_enclaves_map wf_soc_enclaves_map.

End soc_example.
