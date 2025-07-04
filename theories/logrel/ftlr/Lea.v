From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.logrel Require Import ftlr_base interp_weakening.
From cap_machine.program_logic Require Import rules_base rules_Lea.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}
          {contract_enclaves : @CustomEnclavesMap Σ MP}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma lea_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst : RegName) (r : Z + RegName) (P : D):
    ftlr_instr lregs p b e a v lw (Lea dst r) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "[Hcontract #Hsystem_inv] #IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_lea with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst ? Hz Hoffset HincrPC | * Hdst Hz Hoffset HincrPC | ].
    { apply incrementLPC_Some_inv in HincrPC as (p''&b''&e''&a''&v''& ? & HPC & Z & Hregs').

      assert (p'' = p ∧ b'' = b ∧ e'' = e ∧ v'' = v) as (-> & -> & -> & ->).
      { destruct (decide (PC = dst)); subst; by simplify_map_eq. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext.
      iIntros "_".
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]").
      { cbn. intros. subst regs'. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri ? Hri Hvs).
        subst regs'.
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)); simplify_map_eq.
        { unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply interp_weakening; eauto; try solve_addr.
          destruct p0; simpl; auto. }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. } }
      { subst regs'. rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { by rewrite PermFlowsToReflexive. }
    }
    { apply incrementLPC_Some_inv in HincrPC as (p''&b''&e''&a''&v''& ? & HPC & Z & Hregs').

      assert (p'' = p ∧ b'' = b ∧ e'' = e ∧ v'' = v) as (-> & -> & -> & ->).
      { destruct (decide (PC = dst)); subst; by simplify_map_eq. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext.
      iIntros "_".
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]").
      { cbn. intros. subst regs'. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri ? Hri Hvs).
        subst regs'.
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)); simplify_map_eq.
        { unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply (interp_weakening_ot with "Hreg"); auto; try solve_addr.
          apply SealPermFlowsToReflexive. }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. } }
      { subst regs'. rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { by rewrite PermFlowsToReflexive. } }
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
  Qed.

End fundamental.
