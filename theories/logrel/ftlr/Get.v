From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine Require Export ftlr_base.
From cap_machine Require Export rules_Get rules_base.
From cap_machine Require Import stdpp_extra.

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

  Lemma get_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst r : RegName) (ins: instr) (P:D) :
    is_Get ins dst r →
    ftlr_instr lregs p b e a v lw ins P.
  Proof.
    intros Hinstr Hp Hsome i Hbae Hi.
    iIntros "[Hcontract #Hsystem_inv] #IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    rewrite <- Hi in Hinstr. clear Hi.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Get with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementLPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro]. iNext.
      iIntros "_".
      assert (dst <> PC) as HdstPC by (intros ->; by simplify_map_eq).
      simplify_map_eq.
      iApply ("IH" $! (<[dst := _]> (<[PC := _]> lregs)) with "[%] [] [Hmap] [$Hown]");
        try iClear "IH"; eauto.
      { intro. cbn. by repeat (rewrite lookup_insert_is_Some'; right). }
      iIntros (ri v Hri Hsv).
      rewrite insert_commute // lookup_insert_ne // in Hsv; [].
      destruct (decide (ri = dst)); simplify_map_eq.
      { repeat rewrite fixpoint_interp1_eq; auto. }
      { by iApply "Hreg". } rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". }
  Qed.

End fundamental.
