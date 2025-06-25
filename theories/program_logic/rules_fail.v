From Coq Require Import ZArith Lia.
From machine_utils Require Import solve_finz.
From iris.proofmode Require Import proofmode classes.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth.
From iris.algebra.lib Require Import excl_auth.
From cap_machine Require Export logical_mapsto.
From cap_machine Require Export cap_lang iris_extra stdpp_extra.
From cap_machine Require Export wp_opt base_logic.

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

  (* ----------------------------------- FAIL RULES ---------------------------------- *)
  (* Bind Scope expr_scope with language.expr cap_lang. *)

  Lemma wp_notCorrectPC:
    forall E (lw : LWord),
      ~ isCorrectLPC lw ->
      {{{ PC ↦ᵣ lw }}}
         Instr Executable @ E
        {{{ RET FailedV; PC ↦ᵣ lw }}}.
  Proof.
    intros * Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 nt l1 l2 ns) "Hσ1 /="; destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap tbl_cur tbl_prev tbl_all)
        "(Hr & Hm
         & -> & Htbl_cur & Htbl_prev & Htbl_all
         & HEC
         & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
         & %HLinv)"
    ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4.
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iApply fupd_frame_l.
    iSplit. by iPureIntro; apply normal_always_head_reducible.
    iModIntro. iIntros (e1 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    2: eapply state_corresponds_reg_get_word; eauto.
    2: intro contra; apply isCorrectLPC_isCorrectPC_iff in contra; auto.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iFrame. cbn.
    iSplitR "Hϕ HPC"; last by iApply "Hϕ".
    iExists lr, lm, vmap,_,_,_.
    iFrame; auto.
  Qed.

  (* Subcases for respecitvely permissions and bounds *)

  Lemma wp_notCorrectPC_perm E pc_p pc_b pc_e pc_a pc_v :
      pc_p ≠ RX ∧ pc_p ≠ RWX →
      {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]") ; [eapply not_isCorrectLPC_perm; eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  Lemma wp_notCorrectPC_range E pc_p pc_b pc_e pc_a pc_v :
    ¬ (pc_b <= pc_a < pc_e)%a →
    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]") ; [eapply not_isCorrectLPC_bounds; eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_b pc_e pc_a pc_v lw :

    decodeInstrWL lw = Halt →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v) ∗ (pc_a, pc_v) ↦ₐ lw }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v) ∗ (pc_a, pc_v) ↦ₐ lw }}}.

  Proof.
    intros Hinstr Hvpc. apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap tbl_cur tbl_prev tbl_all)
        "(Hr & Hm
         & -> & Htbl_cur & Htbl_prev & Htbl_all
         & HEC
         & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
         & %HLinv)"
    ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4.
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto.
    2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)))
    ; eapply state_corresponds_reg_get_word ; eauto.
    2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto.
    cbn in Hstep. simplify_eq.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iFrame. cbn.
    iSplitR "Hφ Hpc Hpca"; last (iApply "Hφ" ; iFrame).
    iExists lr, lm, vmap,_,_,_.
    iFrame; auto.
  Qed.

  Lemma wp_fail E pc_p pc_b pc_e pc_a pc_v lw :

    decodeInstrWL lw = Fail →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v) ∗ (pc_a, pc_v) ↦ₐ lw }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v) ∗ (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
    intros Hinstr Hvpc. apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap tbl_cur tbl_prev tbl_all)
        "(Hr & Hm
         & -> & Htbl_cur & Htbl_prev & Htbl_all
         & HEC
         & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
         & %HLinv)"
    ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4.
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto.
    2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)))
    ; eapply state_corresponds_reg_get_word ; eauto.
    2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto.
    cbn in Hstep. simplify_eq.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iFrame. cbn.
    iSplitR "Hφ Hpc Hpca"; last (iApply "Hφ" ; iFrame).
    iExists lr, lm, vmap,_,_,_.
    iFrame; auto.
   Qed.

End cap_lang_rules.
