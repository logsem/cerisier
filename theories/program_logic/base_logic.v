From Coq Require Import ZArith Lia.
From machine_utils Require Import solve_finz.
From iris.proofmode Require Import proofmode classes.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import gmap excl agree frac auth.
From iris.algebra.lib Require Import excl_auth.
From cap_machine Require Export logical_mapsto.
From cap_machine Require Export cap_lang iris_extra stdpp_extra.
(* From cap_machine Require Export cap_lang iris_extra stdpp_extra machine_parameters. *)

Section Cerisier_resources.
  Context `{ reservedaddresses : ReservedAddresses}.
(** Instantiation of the program logic *)

Definition enclaves_agreeUR := authR (gmapUR TIndex (agreeR EIdentity)).
Definition EnclavesAgreePreΣ := #[ GFunctor enclaves_agreeUR].
Class EnclavesAgreePreG Σ := {
    EnclavesAgreePre ::  inG Σ enclaves_agreeUR;
}.
Global Instance subG_EnclavesAgreePreΣ {Σ}:
  subG EnclavesAgreePreΣ Σ →
  EnclavesAgreePreG Σ.
Proof. solve_inG. Qed.

Definition enclaves_exclUR := authUR (gmapUR TIndex (exclR EIdentity)).
Definition EnclavesExclPreΣ := #[ GFunctor enclaves_exclUR].
Class EnclavesExclPreG Σ := {
    EnclavesExclPre ::  inG Σ enclaves_exclUR;
}.
Global Instance subG_EnclavesExclPreΣ {Σ}:
  subG EnclavesExclPreΣ Σ →
  EnclavesExclPreG Σ.
Proof. solve_inG. Qed.

Definition ECUR := excl_authUR ENum.
Definition ECPreΣ := #[ GFunctor ECUR].
Class ECPreG Σ := {
    ECPre ::  inG Σ ECUR;
}.
Global Instance subG_ECPreΣ {Σ}:
  subG ECPreΣ Σ →
  ECPreG Σ.
Proof. solve_inG. Qed.

(* CMRΑ for Cerise *)
Class ceriseG Σ := CeriseG {
  cerise_invG : invGS Σ;
  (* Heap for memory *)
  mem_gen_memG :: gen_heapGS LAddr LWord Σ;
  (* Heap for registers *)
  reg_gen_regG :: gen_heapGS RegName LWord Σ;
  enclaves_agree :: EnclavesAgreePreG Σ;
  enclaves_excl :: EnclavesExclPreG Σ;
  (* The ghost resource of deinitialised enclaves *)
  enclaves_name_prev : gname;
  (* The ghost resource of all enclaves that have ever existed *)
  enclaves_name_all : gname;
  (* ghost names for the resources *)
  enclaves_name_cur : gname;
  (* Heap for EC register *)
  EC_G :: ECPreG Σ;
  EC_name : gname;
}.

 (* Assertions over enclaves *)

Definition enclaves_cur (tbl : gmap TIndex EIdentity) `{ceriseG Σ} :=
  own (inG0 := (@EnclavesExclPre Σ enclaves_excl)) enclaves_name_cur (● (Excl <$> tbl)).

Definition enclaves_prev (tbl : gmap TIndex EIdentity) `{ceriseG Σ} :=
  own (inG0 := (@EnclavesAgreePre Σ enclaves_agree)) enclaves_name_prev (● (to_agree <$> tbl)).

Definition enclaves_all (tbl : gmap TIndex EIdentity) `{ceriseG Σ} :=
  own (inG0 := (@EnclavesAgreePre Σ enclaves_agree)) enclaves_name_all (● (to_agree <$> tbl)).

Definition EC_auth `{ceriseG Σ} (n : ENum) :=
  own (inG0 := @ECPre Σ EC_G) EC_name (●E n).

(* Fragmental resources *)

Definition enclave_cur (eid : TIndex) (identity : EIdentity) `{ceriseG Σ} :=
  own (inG0 := (@EnclavesExclPre Σ enclaves_excl)) enclaves_name_cur (auth_frag {[eid := Excl identity]}).

Definition enclave_prev (eid : TIndex) `{ceriseG Σ} : iProp Σ :=
  ∃ id ,
  own (inG0 := (@EnclavesAgreePre Σ enclaves_agree)) enclaves_name_prev (auth_frag {[eid := to_agree id]}).

Definition enclave_all (eid : TIndex) (id : EIdentity) `{ceriseG Σ} : iProp Σ :=
  own (inG0 := (@EnclavesAgreePre Σ enclaves_agree)) enclaves_name_all (auth_frag {[eid := to_agree id]}).

Lemma enclave_all_agree (tidx : TIndex) (id1 id2 : EIdentity) `{ceriseG Σ} :
  enclave_all tidx id1 ∗ enclave_all tidx id2 -∗ ⌜ id1 = id2 ⌝.
Proof.
  iIntros "[E1 E2]".
  iCombine "E1 E2" as "E".
  rewrite own_valid auth_frag_validI.
  iDestruct "E" as "%E".
  rewrite (singleton_valid tidx) in E.
  by apply to_agree_op_inv in E.
Qed.


#[global] Instance enclave_prev_timeless `{ceriseG Σ} (tidx : TIndex)  : Timeless (enclave_prev tidx).
Proof. apply _. Defined.

#[global] Instance enclave_cur_timeless `{ceriseG Σ} (tidx : TIndex) (eid : EIdentity) : Timeless (enclave_cur tidx eid).
Proof. apply _. Defined.

#[global] Instance enclave_all_timeless `{ceriseG Σ} (tidx : TIndex) (eid : EIdentity) : Timeless (enclave_all tidx eid).
Proof. apply _. Defined.

Definition EC_frag `{ceriseG Σ} (n : ENum) : iProp Σ :=
  own (inG0 := @ECPre Σ EC_G) EC_name (excl_auth_frag n).

#[global] Instance EC_timeless `{ceriseG Σ} (n : ENum) : Timeless (EC_frag n).
Proof. apply _. Defined.

End Cerisier_resources.

Lemma enclave_cur_compat `{ceriseG Σ} {tidx eid cur_tb} :
  enclave_cur tidx eid -∗ enclaves_cur cur_tb -∗ ⌜ cur_tb !! tidx = Some eid ⌝.
Proof.
  iIntros "Hcur Hcur_tb".
  iDestruct (own_valid_2 with "Hcur_tb Hcur") as "%Hvalid".
  iPureIntro.
  apply auth_both_valid_discrete in Hvalid.
  destruct Hvalid as (Hincl & _).
  apply singleton_included_l in Hincl.
  destruct Hincl as (I' & HeqI' & HII').
  rewrite lookup_fmap in HeqI'.
  destruct I';
    last by (destruct (cur_tb !! tidx); apply leibniz_equiv in HeqI'; inversion HeqI').
  rewrite Excl_included in HII'.
  apply leibniz_equiv in HII'; subst.
  apply leibniz_equiv in HeqI'.
  destruct (cur_tb !! tidx);
    now inversion HeqI'.
Qed.

Lemma enclave_prev_compat `{ceriseG Σ} {tidx prev_tb} :
  enclave_prev tidx -∗ enclaves_prev prev_tb -∗ ⌜ tidx ∈ dom prev_tb ⌝.
Proof.
  iIntros "(%eid & Hprev) Hprev_tb".
  iDestruct (own_valid_2 with "Hprev_tb Hprev") as "%Hvalid".
  iPureIntro.
  apply auth_both_valid_discrete in Hvalid.
  destruct Hvalid as (Hincl & _).
  apply singleton_included_l in Hincl.
  destruct Hincl as (I' & HeqI' & HII').
  rewrite lookup_fmap in HeqI'.
  destruct (prev_tb !! tidx) eqn:Hptbtidx; last inversion HeqI'.
  now apply (elem_of_dom_2 _ _ _ Hptbtidx).
Qed.


Lemma enclave_update_deinit `{ceriseG Σ} {cur_tb prev_tb tidx I} :
  cur_tb ##ₘ prev_tb ->
  enclaves_cur cur_tb -∗ enclaves_prev prev_tb -∗ enclave_cur tidx I ==∗ enclave_prev tidx ∗ enclaves_cur (delete tidx cur_tb) ∗ enclaves_prev (insert tidx I prev_tb).
Proof.
  iIntros (Hdisj) "Hcur_tb Hprev_tb Hcur".
  iPoseProof (enclave_cur_compat with "Hcur Hcur_tb") as "%Hcurtbtidx".
  iCombine "Hcur_tb Hcur" as "Hcurm".
  iMod (own_update with "Hcurm") as "Hcurm".
  { eapply (auth_update_dealloc _ _ (excl.Excl <$> (delete tidx cur_tb))).
    rewrite fmap_delete.
    now apply (@delete_singleton_local_update TIndex _ _ (excl EIdentity) (Excl <$> cur_tb)).
  }
  iMod (own_update with "Hprev_tb") as "(Hprev_tb & Hprev)".
  { eapply (auth_update_alloc _ (to_agree <$> (insert tidx I prev_tb)) {[ tidx := to_agree I]} ).
    rewrite fmap_insert -insert_empty.
    eapply alloc_singleton_local_update; last done.
    rewrite lookup_fmap.
    enough (prev_tb !! tidx = None) as Hprev_tbNone by now rewrite Hprev_tbNone.
    now apply (map_disjoint_Some_l _ _ _ _ Hdisj Hcurtbtidx).
  }
  iModIntro.
  iSplitL "Hprev".
  - now iExists I.
  - now iFrame.
Qed.


Definition state_interp_logical (σ : cap_lang.state) `{ReservedAddresses} `{!ceriseG Σ} : iProp Σ :=
  ∃ lr lm vmap (cur_tb prev_tb all_tb : gmap TIndex EIdentity) ,
    gen_heap_interp lr ∗
    gen_heap_interp lm ∗
    ⌜cur_tb = σ.(etable)⌝ ∗
    enclaves_cur cur_tb ∗
    enclaves_prev prev_tb ∗
    enclaves_all all_tb ∗
    EC_auth σ.(enumcur) ∗
    ⌜dom cur_tb ## dom prev_tb⌝ ∗
    ⌜dom (cur_tb ∪ prev_tb) = list_to_set (seq 0 σ.(enumcur))⌝ ∗ (**)
    ⌜cur_tb ##ₘ prev_tb⌝ ∗
    ⌜cur_tb ∪ prev_tb = all_tb⌝ ∗
    ⌜state_phys_log_corresponds σ.(reg) σ.(mem) lr lm vmap⌝.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{MachineParameters} `{ReservedAddresses} `{ceriseg: !ceriseG Σ} : irisGS cap_lang Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ := state_interp_logical σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _}.


(* Notations for fragmental resources *)
Notation "EC⤇ n" := (EC_frag n)
                      (at level 20, n at level 50, format "EC⤇ n") : bi_scope.

(* Points to predicates for logical registers *)
Notation "r ↦ᵣ{ q } lw" := (mapsto (L:=RegName) (V:=LWord) r q lw)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q } lw") : bi_scope.
Notation "r ↦ᵣ lw" := (mapsto (L:=RegName) (V:=LWord) r (DfracOwn 1) lw) (at level 20) : bi_scope.

(* Points-to predicates for logical memory *)
Notation "la ↦ₐ{ q } lw" := (mapsto (L:=LAddr) (V:=LWord) la q lw)
  (at level 20, q at level 50, format "la  ↦ₐ{ q }  lw") : bi_scope.
Notation "la ↦ₐ lw" := (mapsto (L:=LAddr) (V:=LWord) la (DfracOwn 1) lw) (at level 20) : bi_scope.

Declare Scope LAddr_scope.
Delimit Scope LAddr_scope with la.

Notation eqb_laddr := (λ (a1 a2: LAddr), (a1.1 =? a2.1)%a && (a1.2 =? a2.2)).
Notation "a1 =? a2" := (eqb_laddr a1 a2) : LAddr_scope.

(* --------------------------- LTAC DEFINITIONS ----------------------------------- *)

(* Ltac destruct_cons_hook ::= destruct_cons_hook2. *)
Ltac inv_head_step :=
  repeat match goal with
         | _ => progress simplify_map_eq/= (* simplify memory stuff *)
         | H : to_val _ = Some _ |- _ => apply of_to_val in H
         | H : _ = of_val ?v |- _ =>
           is_var v; destruct v; first[discriminate H|injection H as H]
         | H : cap_lang.prim_step ?e _ _ _ _ _ |- _ =>
           try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
           (*    and can thus better be avoided. *)
           let φ := fresh "φ" in
           inversion H as [| φ]; subst φ; clear H
         end.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{ reservedaddresses : ReservedAddresses}.
  Context `{MP: MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types la: LAddr.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  (* Conditionally unify on the read register value *)
  Definition read_reg_inr (lregs : LReg) (r : RegName) p b e a v :=
    match lregs !! r with
      | Some (LCap p' b' e' a' v') => (LCap p' b' e' a' v') = LCap p b e a v
      | Some _ => True
      | None => False end.

  (* ------------------------- registers points-to --------------------------------- *)

  Lemma regname_dupl_false r lw1 lw2 :
    r ↦ᵣ lw1 -∗ r ↦ᵣ lw2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (mapsto_valid_2 with "Hr1 Hr2") as %?.
    destruct H. eapply dfrac_full_exclusive in H. auto.
  Qed.

  Lemma regname_neq r1 r2 lw1 lw2 :
    r1 ↦ᵣ lw1 -∗ r2 ↦ᵣ lw2 -∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst r1. iApply (regname_dupl_false with "H1 H2").
  Qed.

  Lemma map_of_regs_1 (r1: RegName) (lw1: LWord) :
    r1 ↦ᵣ lw1 -∗
    ([∗ map] k↦y ∈ <[r1:=lw1]> ∅, k ↦ᵣ y).
  Proof.
    iIntros "H1".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
  Qed.

  Lemma regs_of_map_1 (r1: RegName) (lw1: LWord) :
    ([∗ map] k↦y ∈ {[r1 := lw1]}, k ↦ᵣ y) -∗
    r1 ↦ᵣ lw1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma map_of_regs_2 (r1 r2: RegName) (lw1 lw2: LWord) :
    r1 ↦ᵣ lw1 -∗ r2 ↦ᵣ lw2 -∗
    ([∗ map] k↦y ∈ (<[r1:=lw1]> (<[r2:=lw2]> ∅)), k ↦ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (regname_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_2 (r1 r2: RegName) (lw1 lw2: LWord) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=lw1]> (<[r2:=lw2]> ∅)), k ↦ᵣ y) -∗
    r1 ↦ᵣ lw1 ∗ r2 ↦ᵣ lw2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    apply lookup_insert_None; split; eauto.
  Qed.

  Lemma map_of_regs_3 (r1 r2 r3: RegName) (w1 w2 w3: LWord) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ⌝.
  Proof.
    iIntros "H1 H2 H3".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_3 (r1 r2 r3: RegName) (w1 w2 w3: LWord) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma map_of_regs_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: LWord) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗ r4 ↦ᵣ w4 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r1 ≠ r4 ∧ r2 ≠ r3 ∧ r2 ≠ r4 ∧ r3 ≠ r4 ⌝.
  Proof.
    iIntros "H1 H2 H3 H4".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H1 H4") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    iPoseProof (regname_neq with "H2 H4") as "%".
    iPoseProof (regname_neq with "H3 H4") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: LWord) :
    r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3 ∗ r4 ↦ᵣ w4.
  Proof.
    intros. iIntros "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & ? & _)"; iFrame.
  Qed.

  (* ------------------------- memory points-to --------------------------------- *)

  Lemma addr_dupl_false la lw1 lw2 :
    la ↦ₐ lw1 -∗ la ↦ₐ lw2 -∗ False.
  Proof.
    iIntros "Ha1 Ha2".
    iDestruct (mapsto_valid_2 with "Ha1 Ha2") as %?.
    destruct H. eapply dfrac_full_exclusive in H.
    auto.
  Qed.

  (* -------------- semantic heap + a map of pointsto -------------------------- *)

  Lemma gen_heap_valid_inSepM_general:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (dσ : gmap L (dfrac * V)) (σ : gmap L V)
      (l : L) (dq : dfrac) (v : V),
      dσ !! l = Some (dq, v) →
      gen_heap_interp σ
      -∗ ([∗ map] k↦dqw ∈ dσ, mapsto k dqw.1 dqw.2)
      -∗ ⌜σ !! l = Some v⌝.
  Proof.
    intros * Hσ'.
    rewrite (big_sepM_delete _ dσ l) //. iIntros "? [? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (l : L) (q : Qp) (v : V),
      σ' !! l = Some v →
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜σ !! l = Some v⌝.
  Proof.
    intros * Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "? [? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inSepM':
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜forall (l: L) (v: V), σ' !! l = Some v → σ !! l = Some v⌝.
  Proof.
    intros *. iIntros "? Hmap" (l v Hσ').
    rewrite (big_sepM_delete _ σ' l) //. iDestruct "Hmap" as "[? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inSepM'_general:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (dσ : gmap L (dfrac * V)) (σ : gmap L V) ,
      gen_heap_interp σ
      -∗ ([∗ map] k↦dqw ∈ dσ, mapsto k dqw.1 dqw.2)
      -∗ ⌜forall (l: L) (d : dfrac) (v: V), dσ !! l = Some (d, v) → σ !! l = Some v⌝.
  Proof.
    intros. iIntros "? Hmap" (l d v Hσ).
    rewrite (big_sepM_delete _ dσ l) //.
    iDestruct "Hmap" as "[? ?]". cbn.
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inclSepM_general:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (dσ : gmap L (dfrac * V)) (σ : gmap L V),
      gen_heap_interp σ
      -∗ ([∗ map] k↦dqw ∈ dσ, mapsto k dqw.1 dqw.2)
      -∗ ⌜(fmap snd dσ) ⊆ σ⌝.
  Proof.
    intros. iIntros "Hσ Hmap".
    iDestruct (gen_heap_valid_inSepM'_general with "Hσ Hmap") as "#H". eauto.
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (dσ !! l) eqn:HH'; destruct (σ !! l) eqn:HH
    ; rewrite lookup_fmap HH'
    ; try naive_solver.
    + destruct p; cbn in * ; apply Hincl in HH'; simplify_eq; reflexivity.
    + destruct p; cbn in * ; apply Hincl in HH'; simplify_eq; reflexivity.
    (* + cbn. *)
  Qed.

  Lemma gen_heap_valid_inclSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜σ' ⊆ σ⌝.
  Proof.
    intros *. iIntros "Hσ Hmap".
    iDestruct (gen_heap_valid_inSepM' with "Hσ Hmap") as "#H".
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (σ' !! l) eqn:HH'; destruct (σ !! l) eqn:HH; naive_solver.
  Qed.

  Lemma gen_heap_valid_allSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (EV: Equiv V) (REV: Reflexive EV) (LEV: @LeibnizEquiv V EV)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      (forall (l:L), is_Some (σ' !! l)) →
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜ σ = σ' ⌝.
  Proof.
    intros * ? ? * Hσ'. iIntros "A B".
    iAssert (⌜ forall l, σ !! l = σ' !! l ⌝)%I with "[A B]" as %HH.
    { iIntros (l).
      specialize (Hσ' l). unfold is_Some in Hσ'. destruct Hσ' as [v Hσ'].
      rewrite Hσ'.
      eapply (gen_heap_valid_inSepM _ _ _ _ _ _ σ σ') in Hσ'.
      iApply (Hσ' with "[$]"). eauto. }
    iPureIntro. eapply map_leibniz. intro.
    eapply leibniz_equiv_iff. auto.
    Unshelve.
    unfold equiv. unfold Reflexive. intros [ x |].
    { unfold option_equiv. constructor. apply REV. } constructor.
  Qed.

  Lemma gen_heap_update_inSepM_general :
    ∀ {L V : Type} {EqDecision0 : EqDecision L}
      {H : Countable L} {Σ : gFunctors}
      {gen_heapG0 : gen_heapGS L V Σ}
      (σ : gmap L V) (σ' : gmap L (dfrac * V)) (l : L) (v : V),
      (exists w, (σ' !! l = Some (DfracOwn 1, w))) →
      gen_heap_interp σ
      -∗ ([∗ map] k↦y ∈ σ', mapsto k y.1 y.2)
      ==∗ gen_heap_interp (<[l:=v]> σ)
          ∗ [∗ map] k↦y ∈ (<[l:=(DfracOwn 1, v)]> σ'), mapsto k y.1 y.2.
  Proof.
    intros * Hw. destruct Hw.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=(DfracOwn 1, v)]> σ') l (DfracOwn 1, v)).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.


  Lemma gen_heap_update_inSepM :
    ∀ {L V : Type} {EqDecision0 : EqDecision L}
      {H : Countable L} {Σ : gFunctors}
      {gen_heapG0 : gen_heapGS L V Σ}
      (σ σ' : gmap L V) (l : L) (v : V),
      is_Some (σ' !! l) →
      gen_heap_interp σ
      -∗ ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp (<[l:=v]> σ)
          ∗ [∗ map] k↦y ∈ (<[l:=v]> σ'), mapsto k (DfracOwn 1) y.
  Proof.
    intros * Hσ'. destruct Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=v]> σ') l).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.

  (* Note: glm and lm should really be the same, but the generalization is needed for the inductive case. *)
  Lemma gen_heap_lmem_version_update_addr
    {lmem glm lm lmem' lm': LMem} {vmap vmap': VMap}
      {a : Addr} {v : Version} :
      lmem ⊆ lm ->
      lmem' = update_version_addr glm a v lmem ->
      lm' = update_version_addr glm a v lm ->
      vmap' = update_version_addr_vmap a v vmap ->
      lm !! (a, v+1) = None ->
      is_cur_addr (a,v) vmap ->
      gen_heap_interp lm
      -∗ ([∗ map] k↦y ∈ lmem, mapsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp lm' ∗ [∗ map] k↦y ∈ lmem', mapsto k (DfracOwn 1) y.
  Proof.
    iIntros (Hlmem_incl Hupdlmem Hupdlm Hupdvm Hmaxvm_lm Hcur_lm) "Hgen Hmem".
    rewrite /update_version_addr in Hupdlm, Hupdlmem.
    unfold is_cur_addr in Hcur_lm; cbn in Hcur_lm.
    destruct (glm !! (a,v)) as [lw|]eqn:Hlmav.
    - iMod (((gen_heap_alloc lm (a, v + 1) lw) with "Hgen"))
        as "(Hgen & Ha & _)"; auto.
      iModIntro; subst; iFrame.
      (* local knowledge about (a,v) *)
      iApply (big_sepM_insert with "[Hmem Ha]"); last iFrame.
      eapply lookup_weaken_None; eauto.
    - (*shouldn't happen, but okay *)
      subst. now iFrame.
  Qed.

  (* Note: glm and lm should really be the same, but the generalization is needed for the inductive case. *)
  Lemma gen_heap_lmem_version_update :
    ∀ (glm lmem lm lmem' lm': LMem) (vmap vmap': VMap)
      (la : list Addr) ( v : Version ),
      NoDup la ->
      lmem ⊆ lm ->
      lmem' = update_version_region glm la v lmem ->
      lm' = update_version_region glm la v lm ->
      vmap' = update_version_region_vmap la v vmap ->
      Forall (λ a : Addr, lm !! (a, v+1) = None) la ->
      Forall (λ a : Addr, is_cur_addr (a,v) vmap) la ->
      gen_heap_interp lm
      -∗ ([∗ map] k↦y ∈ lmem, mapsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp lm' ∗ [∗ map] k↦y ∈ lmem', mapsto k (DfracOwn 1) y.
  Proof.
    move=> glm lmem lm lmem' lm' vmap vmap' la.
    move: glm lmem lm lmem' lm' vmap vmap'.
    induction la as [|a la IH]
    ; iIntros
        (glm lmem lm lmem' lm' vmap vmap' v
           HNoDup_la Hlmem_incl Hupdlmem Hupdlm Hupdvmap Hmaxv_lm Hcur_lm)
        "Hgen Hmem".
    - (* no addresses updated *)
      cbn in Hupdlm, Hupdvmap, Hupdlmem; simplify_eq.
      iModIntro; iFrame.
    - destruct_cons.
      iDestruct (IH glm with "Hgen Hmem") as ">[Hgen Hmem]"; eauto.
      simpl in Hupdlmem, Hupdlm, Hupdvmap.
      set (lm'' := update_version_region glm la v lm').
      set (lmem'' := update_version_region glm la v lmem').
      iDestruct (gen_heap_lmem_version_update_addr with "Hgen Hmem") as ">[Hgen Hmem]"; eauto.
      + now apply update_version_region_mono.
      + rewrite <-Hmaxv_lm_a.
        now apply update_version_region_notin_preserves_lmem.
      + unfold is_cur_addr; cbn.
        rewrite (update_version_region_notin_preserves_cur _ _ _ _ _ eq_refl Ha_notin_la).
        exact Hcur_lm_a.
      + now iFrame.
  Qed.

  Lemma prim_step_no_kappa {e1 σ1 κ e2 σ2 efs}:
    prim_step e1 σ1 κ e2 σ2 efs -> κ = [].
  Proof.
    now induction 1.
  Qed.

  Lemma prim_step_no_efs {e1 σ1 κ e2 σ2 efs}:
    prim_step e1 σ1 κ e2 σ2 efs -> efs = [].
  Proof.
    now induction 1.
  Qed.

  (* -------------- predicates on memory maps -------------------------- *)

  Lemma extract_sep_if_split (a pc_a : LAddr) P Q R:
     (if (a =? pc_a)%la then P else Q ∗ R)%I ≡
     ((if (a =? pc_a)%la then P else Q) ∗
     if (a =? pc_a)%la then emp else R)%I.
  Proof.
    destruct (a =? pc_a)%la; auto.
    iSplit; auto. iIntros "[H1 H2]"; auto.
  Qed.

  Lemma memMap_resource_0  :
        True ⊣⊢ ([∗ map] la↦w ∈ ∅, la ↦ₐ w).
  Proof.
    by rewrite big_sepM_empty.
  Qed.

  Lemma memMap_resource_1 (a : LAddr) (w : LWord)  :
        a ↦ₐ w  ⊣⊢ ([∗ map] la↦w ∈ <[a:=w]> ∅, la ↦ₐ w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite delete_insert; last by auto. rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_1_dq (a : LAddr) (w : LWord) dq :
        a ↦ₐ{dq} w  ⊣⊢ ([∗ map] la↦w ∈ <[a:=w]> ∅, la ↦ₐ{dq} w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite delete_insert; last by auto. rewrite big_sepM_empty.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_2ne (a1 a2 : LAddr) (w1 w2 : LWord)  :
    a1 ≠ a2 → ([∗ map] a↦w ∈  <[a1:=w1]> (<[a2:=w2]> ∅), a ↦ₐ w)%I ⊣⊢ a1 ↦ₐ w1 ∗ a2 ↦ₐ w2.
  Proof.
    intros.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite (big_sepM_delete _ _ a2 w2); rewrite delete_insert; try by rewrite lookup_insert_ne. 2: by rewrite lookup_insert.
    rewrite delete_insert; auto.
    rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - iDestruct "HH" as "[H1 [H2 _ ] ]".  iFrame.
    - iDestruct "HH" as "[H1 H2]". iFrame.
  Qed.

  Lemma address_neq la1 la2 lw1 lw2 :
    la1 ↦ₐ lw1 -∗ la2 ↦ₐ lw2 -∗ ⌜la1 ≠ la2⌝.
  Proof.
    iIntros "Ha1 Ha2".
    destruct (finz_eq_dec la1.1 la2.1); auto; subst;
    destruct (Nat.eq_dec la1.2 la2.2); auto; subst;
      try (iPureIntro; congruence).
    iExFalso.
    replace la1 with la2.
    iApply (addr_dupl_false with "[$Ha1] [$Ha2]").
    auto.
    by apply injective_projections.
  Qed.

  Lemma memMap_resource_2ne_apply (la1 la2 : LAddr) (lw1 lw2 : LWord)  :
    la1 ↦ₐ lw1
    -∗ la2 ↦ₐ lw2
    -∗ ([∗ map] la↦lw ∈  <[la1:=lw1]> (<[la2:=lw2]> ∅), la ↦ₐ lw) ∗ ⌜la1 ≠ la2⌝.
  Proof.
    iIntros "Hi Hr2a".
    iDestruct (address_neq  with "Hi Hr2a") as %Hne; auto.
    iSplitL; last by auto.
    iApply memMap_resource_2ne; auto. iSplitL "Hi"; auto.
  Qed.

  Lemma memMap_resource_2gen (la1 la2 : LAddr) (lw1 lw2 : LWord)  :
    ( ∃ lmem, ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∧
       ⌜ if  (la2 =? la1)%la
       then lmem = (<[la1:=lw1]> ∅)
       else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)⌝
    )%I ⊣⊢ (la1 ↦ₐ lw1 ∗ if (la2 =? la1)%la then emp else la2 ↦ₐ lw2) .
  Proof.
    destruct (la2 =? la1)%la eqn:Heq.
    - apply andb_true_iff in Heq ; destruct Heq as [HeqZ HeqV].
      apply Z.eqb_eq, finz_to_z_eq in HeqZ. apply Nat.eqb_eq in HeqV.
      assert (la2 = la1) by (by apply injective_projections).
      rewrite memMap_resource_1.
      iSplit.
      * iDestruct 1 as (lmem) "[HH ->]".  by iSplit.
      * iDestruct 1 as "[Hmap _]". iExists (<[la1:=lw1]> ∅); iSplitL; auto.
    - apply laddr_neq in Heq.
      rewrite -memMap_resource_2ne; auto ; try congruence.
      iSplit.
      + iDestruct 1 as (mem) "[HH ->]" ; done.
      + iDestruct 1 as "Hmap"; iExists (<[la1:=lw1]> (<[la2:=lw2]> ∅)); iSplitL; auto.
  Qed.

  Lemma memMap_resource_2gen_d
    (Φ : LAddr → LWord → iProp Σ)
    (la1 la2 : LAddr) (lw1 lw2 : LWord) :
    ( ∃ lmem, ([∗ map] la↦lw ∈ lmem, Φ la lw) ∧
       ⌜ if (la2 =? la1)%la
       then lmem =  (<[la1:=lw1]> ∅)
       else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)⌝
    ) -∗ (Φ la1 lw1 ∗ if (la2 =? la1)%la then emp else Φ la2 lw2) .
  Proof.
    iIntros "Hmem". iDestruct "Hmem" as (lmem) "[Hmem Hif]".
    destruct ((la2 =? la1)%la) eqn:Heq.
    - iDestruct "Hif" as %->.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
    - iDestruct "Hif" as %->. iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]".
      { rewrite lookup_insert_ne;auto. apply laddr_neq in Heq; congruence. }
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
  Qed.

  Lemma memMap_resource_2gen_d_dq (Φ : LAddr → dfrac → LWord → iProp Σ)
    (la1 la2 : LAddr) (dq1 dq2 : dfrac) (lw1 lw2 : LWord)  :
    ( ∃ lmem dfracs, ([∗ map] la↦dlw ∈ prod_merge dfracs lmem, Φ la dlw.1 dlw.2) ∧
       ⌜ (if  (la2 =? la1)%la
          then lmem = <[la1:=lw1]> ∅
          else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)) ∧
       (if  (la2 =? la1)%la
       then dfracs = <[la1:=dq1]> ∅
       else dfracs = <[la1:=dq1]> (<[la2:=dq2]> ∅))⌝
    ) -∗ (Φ la1 dq1 lw1 ∗ if (la2 =? la1)%la then emp else Φ la2 dq2 lw2) .
  Proof.
    iIntros "Hmem". iDestruct "Hmem" as (mem dfracs) "[Hmem [Hif Hif'] ]".
    destruct ((la2 =? la1)%la) eqn:Heq.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,lw1));auto. rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,lw1));auto.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,lw2));auto.
      rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]".
      { rewrite lookup_insert_ne;auto. apply laddr_neq in Heq; congruence. }
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
  Qed.

  (* Not the world's most beautiful lemma, but it does avoid us having to fiddle around with a later under an if in proofs *)
  Lemma memMap_resource_2gen_clater (la1 la2 : LAddr) (lw1 lw2 : LWord) (Φ : LAddr -> LWord -> iProp Σ) :
    (▷ Φ la1 lw1)
    -∗ (if (la2 =? la1)%la then emp else ▷ Φ la2 lw2)
    -∗ (∃ lmem, ▷ ([∗ map] la↦lw ∈ lmem, Φ la lw) ∗
                  ⌜if  (la2 =? la1)%la
        then lmem = <[la1:=lw1]> ∅
        else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)⌝
       )%I.
  Proof.
    iIntros "Hc1 Hc2".
    destruct (la2 =? la1)%la eqn:Heq.
    - iExists (<[la1:= lw1]> ∅); iSplitL; auto. iNext. iApply big_sepM_insert;[|by iFrame].
      auto.
    - iExists (<[la1:=lw1]> (<[la2:=lw2]> ∅)); iSplitL; auto.
      iNext.
      iApply big_sepM_insert;[|iFrame].
      { rewrite lookup_insert_ne;auto. apply laddr_neq in Heq; congruence. }
      iApply big_sepM_insert;[|by iFrame]. auto.
  Qed.

  (* More general lemmas *)
   Lemma memMap_resource_2gen_clater_dq (la1 la2 : LAddr) (dq1 dq2 : dfrac) (lw1 lw2 : LWord) (Φ : LAddr -> dfrac → LWord -> iProp Σ)  :
    (▷ Φ la1 dq1 lw1) -∗
    (if (la2 =? la1)%la then emp else ▷ Φ la2 dq2 lw2) -∗
    (∃ lmem dfracs, ▷ ([∗ map] la↦dlw ∈ prod_merge dfracs lmem, Φ la dlw.1 dlw.2) ∗
       ⌜(if  (la2 =? la1)%la
       then lmem = <[la1:=lw1]> ∅
       else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)) ∧
       (if  (la2 =? la1)%la
       then dfracs = (<[la1:=dq1]> ∅)
       else dfracs = <[la1:=dq1]> (<[la2:=dq2]> ∅))⌝
    )%I.
  Proof.
    iIntros "Hc1 Hc2".
    destruct (la2 =? la1)%la eqn:Heq.
    - iExists (<[la1:= lw1]> ∅),(<[la1:= dq1]> ∅); iSplitL; auto. iNext.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,lw1));auto. rewrite merge_empty.
      iApply big_sepM_insert;[|by iFrame].
      auto.
    - iExists (<[la1:=lw1]> (<[la2:=lw2]> ∅)),(<[la1:=dq1]> (<[la2:=dq2]> ∅)); iSplitL; auto.
      iNext.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,lw1));auto.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,lw2));auto.
      rewrite merge_empty.
      iApply big_sepM_insert;[|iFrame].
      { rewrite lookup_insert_ne;auto. apply laddr_neq in Heq; congruence. }
      iApply big_sepM_insert;[|by iFrame]. auto.
  Qed.

  Lemma memMap_delete:
    ∀ (la : LAddr) (lw : LWord) lmem,
      lmem !! la = Some lw →
      ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw)
      ⊣⊢ (la ↦ₐ lw ∗ ([∗ map] k↦y ∈ delete la lmem, k ↦ₐ y)).
  Proof.
    intros la lw lmem Hmem.
    rewrite -(big_sepM_delete _ _ la); auto.
  Qed.

 Lemma mem_remove_dq lmem dq :
    ([∗ map] la↦lw ∈ lmem, la ↦ₐ{dq} lw) ⊣⊢
    ([∗ map] la↦dw ∈ (prod_merge (create_gmap_default (elements (dom lmem)) dq) lmem), la ↦ₐ{dw.1} dw.2).
  Proof.
    iInduction (lmem) as [|la k lmem] "IH" using map_ind.
    - rewrite big_sepM_empty dom_empty_L elements_empty
              /= /prod_merge merge_empty big_sepM_empty. done.
    - rewrite dom_insert_L.
      assert (elements ({[la]} ∪ dom lmem) ≡ₚ la :: elements (dom lmem)) as Hperm.
      { apply elements_union_singleton. apply not_elem_of_dom. auto. }
      apply (create_gmap_default_permutation _ _ dq) in Hperm. rewrite Hperm /=.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq,k)) //.
      iSplit.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        iApply big_sepM_insert.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom lmem)) dq !! la);auto; rewrite H;auto. }
        iFrame. iApply "IH". iFrame.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom lmem)) dq !! la);auto; rewrite H;auto. }
        iApply big_sepM_insert. auto.
        iFrame. iApply "IH". iFrame.
  Qed.

  (* a more general version of load to work also with any fraction and persistent points tos *)
  Lemma gen_mem_valid_inSepM_general:
    ∀ (lmem : gmap LAddr (dfrac * LWord)) (lmem' : LMem)
      (la : LAddr) (lw : LWord) (dq : dfrac),
      lmem !! la = Some (dq, lw) →
      gen_heap_interp lmem'
      -∗ ([∗ map] a↦dqw ∈ lmem, a ↦ₐ{ dqw.1 } dqw.2)
      -∗ ⌜lmem' !! la = Some lw⌝.
  Proof.
    iIntros (lmem lmem' la lw dq Hmem_pc) "Hm Hmem".
    iDestruct (big_sepM_delete _ _ la with "Hmem") as "[Hpc_a Hmem]"; eauto.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %?; auto.
  Qed.

  Lemma gen_mem_valid_inSepM:
    ∀ (lmem lm : LMem) (la : LAddr) (lw : LWord),
      lmem !! la = Some lw →
      gen_heap_interp lm
      -∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw)
      -∗ ⌜lm !! la = Some lw⌝.
  Proof.
    iIntros (lmem lm la lw Hmem_pc) "Hm Hmem".
    iDestruct (memMap_delete la with "Hmem") as "[Hpc_a Hmem]"; eauto.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %?; auto.
  Qed.

  Lemma gen_mem_update_inSepM :
    ∀ {Σ : gFunctors} {gen_heapG0 : gen_heapGS Addr Word Σ}
      (lmem lmem': LMem) (la : LAddr) (lw lw' : LWord),
      lmem' !! la = Some lw' →
      gen_heap_interp lmem
      -∗ ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw)
      ==∗ gen_heap_interp (<[la:=lw]> lmem)
          ∗ ([∗ map] a↦w ∈ <[la:=lw]> lmem', a ↦ₐ w).
  Proof.
    intros.
    rewrite (big_sepM_delete _ _ la);[|eauto].
    iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]"; eauto.
    iModIntro.
    iSplitL "Hh"; eauto.
    iDestruct (big_sepM_insert _ _ la with "[$Hmap $Hl]") as "H".
    apply lookup_delete.
    rewrite insert_delete_insert. iFrame.
  Qed.


  (* ----------------------------------- PURE RULES ---------------------------------- *)

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_exec_pure := intros ?; apply nsteps_once, pure_head_step_pure_step;
                                constructor; [solve_exec_safe|]; intros;
                                (match goal with
                                | H : head_step _ _ _ _ _ _ |- _ => inversion H end).

  Global Instance pure_seq_failed :
    PureExec True 1 (Seq (Instr Failed)) (Instr Failed).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_halted :
    PureExec True 1 (Seq (Instr Halted)) (Instr Halted).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_done :
    PureExec True 1 (Seq (Instr NextI)) (Seq (Instr Executable)).
  Proof. by solve_exec_pure. Qed.

End cap_lang_rules.

(* Used to close the failing cases of the ftlr.
  - Hcont is the (iris) name of the closing hypothesis (usually "Hφ")
  - fail_case_name is one constructor of the spec_name,
    indicating the appropriate error case
 *)
Ltac iFailCore fail_case_name :=
      iPureIntro;
      econstructor; eauto;
      eapply fail_case_name ; eauto.

Ltac iFailWP Hcont fail_case_name :=
  by (cbn; iFrame; iApply Hcont; iFrame; iFailCore fail_case_name).

(* ----------------- useful definitions to factor out the wp specs ---------------- *)

(*--- register equality ---*)
  Lemma addr_ne_reg_ne {regs : leibnizO Reg} {r1 r2 : RegName}
        {p0 b0 e0 a0 p b e a}:
    regs !! r1 = Some (WCap p0 b0 e0 a0)
    → regs !! r2 = Some (WCap p b e a)
    → a0 ≠ a → r1 ≠ r2.
  Proof.
    intros Hr1 Hr2 Hne.
    destruct (decide (r1 = r2)); simplify_eq; auto.
  Qed.

(*--- regs_of ---*)

Definition regs_of_argument (arg: Z + RegName): gset RegName :=
  match arg with
  | inl _ => ∅
  | inr r => {[ r ]}
  end.

Definition regs_of (i: instr): gset RegName :=
  match i with
  | Lea r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | GetP r1 r2 => {[ r1; r2 ]}
  | GetB r1 r2 => {[ r1; r2 ]}
  | GetE r1 r2 => {[ r1; r2 ]}
  | GetA r1 r2 => {[ r1; r2 ]}
  | GetOType dst src => {[ dst; src ]}
  | GetWType dst src => {[ dst; src ]}
  | Add r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Sub r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Mod r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Lt r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | HashConcat r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Hash r1 r2 => {[ r1; r2 ]}
  | Mov r arg => {[ r ]} ∪ regs_of_argument arg
  | Restrict r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Subseg r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Load r1 r2 => {[ r1; r2 ]}
  | Store r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Jnz r1 r2 => {[ r1; r2 ]}
  | Seal dst r1 r2 => {[dst; r1; r2]}
  | UnSeal dst r1 r2 => {[dst; r1; r2]}
  | IsUnique dst src => {[dst; src]}
  | EInit r1 r2 => {[r1;r2]}
  | EDeInit r => {[r]}
  | EStoreId rs rd => {[rs; rd]}
  | _ => ∅
  end.

Lemma indom_regs_incl D (regs regs': Reg) :
  D ⊆ dom regs →
  regs ⊆ regs' →
  ∀ r, r ∈ D →
       ∃ (w:Word), (regs !! r = Some w) ∧ (regs' !! r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (regs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset RegName). typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
Qed.

Lemma indom_lregs_incl D (lregs lregs': LReg) :
  D ⊆ dom lregs →
  lregs ⊆ lregs' →
  ∀ r, r ∈ D →
       ∃ (w:LWord), (lregs !! r = Some w) ∧ (lregs' !! r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (lregs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset RegName). typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
  Qed.

(*--- incrementPC ---*)

Definition incrementPC (regs: Reg) : option Reg :=
  match regs !! PC with
  | Some (WCap p b e a) =>
    match (a + 1)%a with
    | Some a' => Some (<[ PC := WCap p b e a' ]> regs)
    | None => None
    end
  | _ => None
  end.

Lemma incrementPC_Some_inv regs regs' :
  incrementPC regs = Some regs' ->
  exists p b e a a',
    regs !! PC = Some (WCap p b e a) ∧
    (a + 1)%a = Some a' ∧
    regs' = <[ PC := WCap p b e a' ]> regs.
Proof.
  unfold incrementPC.
  destruct (regs !! PC) as [ [ | [? ? ? u | ] | ] | ];
    try congruence.
  case_eq (u+1)%a; try congruence. intros ? ?. inversion 1.
  do 5 eexists. split; eauto.
Qed.

Lemma incrementPC_None_inv regs pg b e a :
  incrementPC regs = None ->
  regs !! PC = Some (WCap pg b e a) ->
  (a + 1)%a = None.
Proof.
  unfold incrementPC.
  destruct (regs !! PC) as [ [ | [? ? ? u | ] | ] |];
    try congruence.
  case_eq (u+1)%a; congruence.
Qed.

Lemma incrementPC_overflow_mono regs regs' :
  incrementPC regs = None →
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  incrementPC regs' = None.
Proof.
  intros Hi HPC Hincl. unfold incrementPC in *. destruct HPC as [c HPC].
  pose proof (lookup_weaken _ _ _ _ HPC Hincl) as HPC'.
  rewrite HPC HPC' in Hi |- *. destruct c as [| [? ? ? aa | ] | ]; auto.
  destruct (aa+1)%a; last by auto. congruence.
Qed.

Lemma incrementPC_overflow_antimono regs regs' :
  incrementPC regs = None →
  regs' ⊆ regs →
  incrementPC regs' = None.
Proof.
  intros Hi Hincl. unfold incrementPC in *.
  destruct (regs' !! PC) eqn:HrpPC; last easy.
  rewrite (lookup_weaken _ _ _ _ HrpPC Hincl) in Hi.
  destruct w; try easy.
  destruct sb; try easy.
  now destruct (a + 1)%a.
Qed.

(* todo: instead, define updatePC on top of incrementPC *)
Lemma incrementPC_fail_updatePC regs m etbl ecur:
   incrementPC regs = None ->
   updatePC {| reg := regs; mem := m; etable := etbl ; enumcur := ecur |} = None.
Proof.
   rewrite /incrementPC /updatePC /=.
   destruct (regs !! PC) as [X|]; auto.
   destruct X as [| [? ? ? a' | ] |]; auto.
   destruct (a' + 1)%a; auto. congruence.
Qed.

Lemma incrementPC_success_updatePC regs m etbl ecur regs' :
  incrementPC regs = Some regs' ->
  ∃ p b e a a',
    regs !! PC = Some (WCap p b e a) ∧
    (a + 1)%a = Some a' ∧
    updatePC {| reg := regs; mem := m; etable := etbl ; enumcur := ecur |} =
      Some (NextI,
          {| reg := <[ PC := WCap p b e a' ]> regs; mem := m; etable := etbl ; enumcur := ecur |}) ∧
    regs' = <[ PC := WCap p b e a' ]> regs.
Proof.
  rewrite /incrementPC /updatePC /update_reg /=.
  destruct (regs !! PC) as [X|] eqn:?; auto; try congruence; [].
  destruct X as [| [? ? ? a'|]|] eqn:?; try congruence; [].
  destruct (a' + 1)%a eqn:?; [| congruence]. inversion 1; subst regs'.
  do 5 eexists. repeat split; auto.
Qed.

Lemma updatePC_success_incl m m' regs regs' etbl etbl' ecur ecur' w :
  regs ⊆ regs' →
  updatePC {| reg := regs; mem := m; etable := etbl ; enumcur := ecur |}
    = Some (NextI, {| reg := <[ PC := w ]> regs; mem := m; etable := etbl ; enumcur := ecur |}) →
  updatePC {| reg := regs'; mem := m'; etable := etbl' ; enumcur := ecur' |}
  = Some (NextI, {| reg := <[ PC := w ]> regs'; mem := m'; etable := etbl' ; enumcur := ecur' |}).
Proof.
  intros * Hincl Hu. rewrite /updatePC /= in Hu |- *.
  destruct (regs !! PC) as [ w1 |] eqn:Hrr.
  { pose proof (lookup_weaken _ _ _ _ Hrr Hincl) as Hregs'. rewrite Hregs'.
    destruct w1 as [|[ ? ? ? a1|] | ]; simplify_eq.
    destruct (a1 + 1)%a eqn:Ha1; simplify_eq. rewrite /update_reg /=.
    f_equal. f_equal.
    assert (HH: forall (reg1 reg2:Reg), reg1 = reg2 -> reg1 !! PC = reg2 !! PC)
      by (intros * ->; auto).
    unfold update_reg in Hu; cbn in Hu.
    injection Hu; intros.
    apply HH in H. rewrite !lookup_insert in H. by simplify_eq. }
  {  inversion Hu. }
Qed.

Lemma updatePC_fail_incl m m' regs regs' etbl etbl' ecur ecur'  :
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  updatePC {| reg := regs; mem := m; etable := etbl ; enumcur := ecur |} = None →
  updatePC {| reg := regs'; mem := m'; etable := etbl' ; enumcur := ecur' |} = None.
Proof.
  intros [w HPC] Hincl Hfail. rewrite /updatePC /= in Hfail |- *.
  rewrite !HPC in Hfail. have -> := lookup_weaken _ _ _ _ HPC Hincl.
  destruct w as [| [? ? ? a1 | ] |]; simplify_eq; auto;[].
  destruct (a1 + 1)%a; simplify_eq; auto.
Qed.

Ltac incrementPC_inv :=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?)
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H
  end; simplify_eq.

Lemma updatePC_incrementPC {φ} :
  updatePC φ =
    r' ← incrementPC (reg φ) ;
    Some (NextI , update_regs φ r').
Proof.
  unfold updatePC, incrementPC.
  destruct (reg φ !! PC); try now cbn.
  unfold update_reg, update_regs.
  destruct w; try now cbn.
  destruct sb; try now cbn.
  destruct (a + 1)%a; try now cbn.
Qed.

(*--- incrementLPC ---*)

Definition incrementLPC (regs: LReg) : option LReg :=
  match regs !! PC with
  | Some (LCap p b e a v) =>
    match (a + 1)%a with
    | Some a' => Some (<[ PC := LCap p b e a' v ]> regs)
    | None => None
    end
  | _ => None
  end.

Lemma incrementLPC_Some_inv lregs lregs' :
  incrementLPC lregs = Some lregs' ->
  exists p b e a v a',
    lregs !! PC = Some (LCap p b e a v) ∧
      (a + 1)%a = Some a' ∧
      lregs' = <[ PC := (LCap p b e a' v) ]> lregs.
Proof.
  rewrite /incrementLPC.
  destruct (lregs !! PC) as [ [ | [? ? ? u ? | ] | ] | ]; try congruence.
  case_eq (u+1)%a; try congruence.
  intros ? ?. inversion 1.
  do 6 eexists. split; eauto.
Qed.

Lemma incrementLPC_None_inv lregs pg b e a v :
  incrementLPC lregs = None ->
  lregs !! PC = Some (LCap pg b e a v) ->
  (a + 1)%a = None.
Proof.
  unfold incrementLPC.
  destruct (lregs !! PC) as [ [ | [? ? ? u ? | ] | ] |]; try congruence.
  case_eq (u+1)%a; congruence.
Qed.

Ltac incrementLPC_inv :=
  match goal with
  | H : incrementLPC _ = Some _ |- _ =>
    apply incrementLPC_Some_inv in H as (?&?&?&?&?&?&?&?&?)
  | H : incrementLPC _ = None |- _ =>
    eapply incrementLPC_None_inv in H
  end; simplify_eq.

Tactic Notation "incrementLPC_inv" "as" simple_intropattern(pat):=
  match goal with
  | H : incrementLPC _ = Some _ |- _ =>
    apply incrementLPC_Some_inv in H as pat
  | H : incrementLPC _ = None |- _ =>
    eapply incrementLPC_None_inv in H
  end; simplify_eq.
