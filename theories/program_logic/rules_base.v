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

  Lemma wp_cap_lang {s E} {Φ} : ∀ e1 : language.expr cap_ectx_lang,
      to_val e1 = None →
      (∀ (σ1 : language.state cap_ectx_lang),
            state_interp_logical σ1 ={E}=∗
              ⌜head_reducible e1 σ1⌝ ∗
              ▷(∀ (e2 : language.expr cap_ectx_lang)
                  (σ2 : ectx_language.state cap_ectx_lang),
                  ⌜prim_step e1 σ1 [] e2 σ2 []⌝ -∗
                                                   £ 1 ={E}=∗ state_interp_logical σ2 ∗ from_option Φ False (language.to_val e2)))
        ⊢ wp s E e1 Φ.
  Proof.
    iIntros (? Hnoval) "H".
    iApply wp_lift_atomic_head_step_no_fork; try assumption.
    iIntros (σ1 ns κ κs nt) "Hσ1 /=".
    iMod ("H" $! σ1 with "[$Hσ1]") as "[%Hred H]".
    iModIntro. iSplitR; first by iPureIntro.
    iModIntro. iIntros (? ? ?) "%Hstep Hcred".
    destruct (prim_step_no_efs Hstep).
    destruct (prim_step_no_kappa Hstep).
    iMod ("H" $! e2 σ2 Hstep with "Hcred") as "H".
    now iSplitR.
  Qed.

  Lemma wp_instr_exec {s E} {Φ} :
      (∀ (σ1 : language.state cap_ectx_lang),
            state_interp_logical σ1 ={E}=∗
              ▷(∀ (e2 : ConfFlag)
                  (σ2 : ExecConf),
                  ⌜step (Executable, σ1) (e2, σ2)⌝ -∗
                                                   £ 1 ={E}=∗ state_interp_logical σ2 ∗ from_option Φ False (language.to_val (Instr e2))))
        ⊢ wp s E (Instr Executable) Φ.
  Proof.
    iIntros "H".
    iApply wp_cap_lang; first easy.
    iIntros (σ1) "Hσ1".
    iMod ("H" $! _ with "Hσ1") as "H".
    iModIntro. iSplitR.
    { iPureIntro. apply normal_always_head_reducible. }
    iModIntro.
    iIntros (e2 σ2) "%Hstep".
    destruct (prim_step_exec_inv _ _ _ _ _ Hstep) as (_ & _ & c & -> & Hstep2).
    now iApply "H".
  Qed.


  Lemma wp_lift_atomic_head_step_no_fork_determ {s E Φ} e1 :
    to_val e1 = None →
    (∀ (σ1:cap_lang.state) ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
     ∃ κ e2 (σ2:cap_lang.state) efs, ⌜cap_lang.prim_step e1 σ1 κ e2 σ2 efs⌝ ∗
      (▷ |==> (state_interp σ2 (S ns) κs nt ∗ from_option Φ False (to_val e2))))
      ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns κ κs nt)  "Hσ1 /=".
    iMod ("H" $! σ1 ns κ κs nt with "[Hσ1]") as "H"; auto.
    iDestruct "H" as (κ' e2 σ2 efs) "[H1 H2]".
    iModIntro. iSplit.
    - rewrite /head_reducible /=.
      iExists κ', e2, σ2, efs. auto.
    - iNext. iIntros (? ? ?) "H".
      iDestruct "H" as %Hs1.
      iDestruct "H1" as %Hs2.
      destruct (cap_lang_determ _ _ _ _ _ _ _ _ _ _ Hs1 Hs2) as [Heq1 [Heq2 [Heq3 Heq4]]].
      subst. iMod "H2". iIntros "_".
      iModIntro. iFrame. inv Hs1; auto.
  Qed.

  Lemma wp_instr_exec_opt {s E Φ pc_a pc_v dq regs lw pc_p pc_b pc_e instr} :
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    decodeInstrWL lw = instr →
    regs_of instr ⊆ dom regs →
    ((▷ (pc_a, pc_v) ↦ₐ{dq} lw) ∗
     (▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
      ▷ (∀ (σ1 : language.state cap_ectx_lang),
            state_interp_logical σ1 ∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗ (pc_a, pc_v) ↦ₐ{dq} lw ={E}=∗
              (∀ wa,
                  ⌜ (reg σ1) !! PC = Some (WCap pc_p pc_b pc_e pc_a) /\
                    (mem σ1) !! pc_a = Some wa /\
                    isCorrectPC (WCap pc_p pc_b pc_e pc_a) /\
                    decodeInstrW wa = instr ⌝ -∗ £ 1 ={E}=∗
                 wp_opt (exec_opt instr σ1) (|={E}=> state_interp_logical σ1 ∗ Φ FailedV)
                 (fun (c2 : Conf) => |={E}=> (state_interp_logical c2.2 ∗ from_option Φ False (language.to_val (Instr c2.1))))))
        ⊢ wp s E (Instr Executable) Φ).
  Proof.
    iIntros (Hcorrpc Hregspc Hdecode Hregs_incl) "(>Hcode & >Hregs & H)".
    apply isCorrectLPC_isCorrectPC_iff in Hcorrpc; cbn in Hcorrpc.
    iApply wp_instr_exec.
    iIntros (σ1) "Hσ1".
    destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap tbl_cur tbl_prev tbl_all)
        "(Hr & Hm
         & -> & Htbl_cur & Htbl_prev & Htbl_all
         & HEC
         & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
         & %HLinv)"
    ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4.
    iModIntro.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hregsincl".
    have Hregs_pc := lookup_weaken _ _ _ _ Hregspc Hregsincl.
    iDestruct (@gen_heap_valid with "Hm Hcode") as %Hlcode; auto.
    iModIntro.
    iIntros (e2 σ2 Hstep) "Hcred".
    iMod ("H" $! {| reg := reg; mem := mem; etable := etable; enumcur := enumcur |} with
           "[Hr Hm Htbl_cur Htbl_prev Htbl_all $HEC $Hregs $Hcode]") as "H".
    { iExists _, _, _,_,_,_. now iFrame.
      (* TODO: allow changing cur_map? *)
    }

    eapply step_exec_inv in Hstep; eauto; cbn.
    2: eapply state_corresponds_reg_get_word_cap ; eauto.
    2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto.

    iMod ("H" $! (lword_get_word lw) with "[%] Hcred") as "H".
    { intuition.
      + now eapply (state_corresponds_reg_get_word _ _ _ _ _ _ (LCap pc_p pc_b pc_e pc_a pc_v) HLinv).
      + eapply (state_corresponds_mem_get_word _ _ _ _ _ pc_a pc_v lw HLinv )
        ; try now cbn.
        eapply state_corresponds_cap_cur_word ; [ apply HLinv | | | | apply Hregs_pc | ]
        ; try now cbn.
        eapply (isCorrectPC_withinBounds _ _ _ _ Hcorrpc).
    }
    unfold exec in Hstep.
    destruct (exec_opt instr {| reg := reg; mem := mem; etable := etable; enumcur := enumcur |});
    now inversion Hstep.
  Qed.












  Definition state_interp_with_res (φt : ExecConf) (lrt : LReg) (lmt : LMemF) : iProp Σ :=
    (state_interp_logical φt ∗ ([∗ map] k↦y ∈ lrt, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ lmt, k ↦ₐ{y.1} y.2)).

  Definition state_interp_transient (φ φt : ExecConf) (lr lrt : LReg) (lm lmt : LMemF) : iProp Σ :=
    transiently
      (state_interp_with_res φ lr lm)
      (state_interp_with_res φt lrt lmt).

  Lemma state_interp_corr {σ lregs} {lmem : LMemF} :
    state_interp_with_res σ lregs lmem ⊢
      ⌜ ∃ lreg_t lmem_t cur_map,
         lregs ⊆ lreg_t /\ (snd <$> lmem) ⊆ lmem_t /\
        state_phys_log_corresponds σ.(reg) σ.(mem) lreg_t lmem_t cur_map ⌝.
  Proof.
    iIntros "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm vmap tbl_cur tbl_prev tbl_all)
        "(Hr & Hm
         & -> & Htbl_cur & Htbl_prev & Htbl_all
         & HEC
         & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
         & %HLinv)"
    ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iPoseProof (gen_heap_valid_inclSepM_general with "Hm Hmem") as "%Hlmem_incl".
    now iExists lr, lm, vmap.
  Qed.

  Lemma state_interp_transient_intro {φ : ExecConf} {lr : LReg} {lm : LMemF} :
    state_interp_with_res φ lr lm
                ⊢ state_interp_transient φ φ lr lr lm lm.
  Proof. iIntros. now iApply transiently_intro. Qed.

  (* TODO: split off lemma about big_sepM_fmap?  *)
  Lemma state_interp_transient_intro_nodfracs {φ : ExecConf} {lr : LReg} {lm : LMem} :
    state_interp_logical φ ∗ ([∗ map] k↦y ∈ lr, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ lm, k ↦ₐ y)
      ⊢ state_interp_transient φ φ lr lr ((fun y => (DfracOwn 1 , y)) <$> lm) ((fun y => (DfracOwn 1 , y)) <$> lm).
  Proof.
    iIntros "H".
    iApply state_interp_transient_intro.
    iDestruct "H" as "($ & $ & Hm)".
    now rewrite big_sepM_fmap.
  Qed.

  Lemma state_interp_transient_elim_abort {φ φt: ExecConf} {lr lrt : LReg} {lm lmt : LMemF} :
    state_interp_transient φ φt lr lrt lm lmt
      ⊢ state_interp_with_res φ lr lm.
  Proof.
    now iIntros "(H & _)".
  Qed.

  Lemma state_interp_transient_elim_commit
    {φ φt: ExecConf} {lr lrt : LReg} {lm lmt : LMemF}:
    state_interp_transient φ φt lr lrt lm lmt ⊢
      |==> state_interp_with_res φt lrt lmt.
  Proof.
    eapply transiently_commit.
  Qed.

  Lemma state_interp_transient_corr {φ φt lr lrt lm lmt} :
    state_interp_transient φ φt lr lrt lm lmt ⊢
      ⌜ ∃ lreg_t lmem_t cur_map,
        lrt ⊆ lreg_t /\ snd <$> lmt ⊆ lmem_t /\
          state_phys_log_corresponds φt.(reg) φt.(mem) lreg_t lmem_t cur_map ⌝.
  Proof.
    iIntros "Htr".
    iMod (transiently_commit with "Htr") as "Hσrt".
    iDestruct (state_interp_corr with "Hσrt") as "%Hcor".
    destruct Hcor as (lreg_t & lmem_t & cur_map & Hlreg_t & Hlmem_t & Hsplc).
    now iExists lreg_t, lmem_t, cur_map.
  Qed.

  Lemma wp2_reg_lookup5 {lrt lreg_t lmem_t r σr σm vmap}:
    r ∈ dom lrt ->
    lrt ⊆ lreg_t ->
    state_phys_log_corresponds σr σm lreg_t lmem_t vmap ->
    ⊢ wp_opt2 (lrt !! r) (σr !! r) (False : iProp Σ) (fun lrw rw => ⌜ rw = lword_get_word lrw ⌝).
  Proof.
    iIntros (Hdom Hregs_incl HInv).
    destruct (proj1 (elem_of_dom lrt r) Hdom) as (lrw & Hlrt).
    rewrite Hlrt.
    rewrite map_subseteq_spec in  Hregs_incl.
    specialize (Hregs_incl r lrw Hlrt).
    eapply state_corresponds_reg_get_word in Hregs_incl; eauto.
    erewrite Hregs_incl.
    now iApply wp2_val.
  Qed.

  Lemma wp2_reg_lookup4 {lrt lmt r φt Φf} :
    r ∈ dom lrt ->
    state_interp_with_res φt lrt lmt ⊢
      wp_opt2 (lrt !! r) (reg φt !! r) Φf (fun lrw rw => ⌜ rw = lword_get_word lrw ⌝ ∗ state_interp_with_res φt lrt lmt).
  Proof.
    iIntros (Hdom) "Hσ".
    iDestruct (state_interp_corr with "Hσ") as "%HInv".
    destruct HInv as (lregs_t & lmem_t & cur_map & Hregs_incl & Hmem_incl & HInv).
    destruct (proj1 (elem_of_dom lrt r) Hdom) as (lrw & Hlrt).
    rewrite Hlrt.
    rewrite map_subseteq_spec in  Hregs_incl.
    specialize (Hregs_incl r lrw Hlrt).
    eapply state_corresponds_reg_get_word in Hregs_incl; eauto.
    erewrite Hregs_incl.
    iApply wp2_val.
    now iSplitR.
  Qed.

  Lemma wp2_reg_lookup3 {lrt lmt r φt Φs Φf} :
      r ∈ dom lrt ->
      state_interp_with_res φt lrt lmt ∗
        (∀ lwr, state_interp_with_res φt lrt lmt -∗ Φs lwr (lword_get_word lwr)) ⊢
        wp_opt2 (lrt !! r) (reg φt !! r) Φf Φs.
  Proof.
    iIntros (Hdom) "(Hσ & Hk)".
    iPoseProof (wp2_reg_lookup4 Hdom with "Hσ") as "Hwp".
    iApply (wp_opt2_mono with "[Hk $Hwp]").
    iIntros (lwr wr) "(-> & Hσ)".
    now iApply ("Hk" with "Hσ").
  Qed.

  Lemma wp2_reg_lookup2 {lrt lmt r φ φt lr lm Φf} :
    r ∈ dom lrt ->
    state_interp_transient φ φt lr lrt lm lmt ⊢
      wp_opt2 (lrt !! r) (reg φt !! r) Φf (fun lrw rw => ⌜ rw = lword_get_word lrw ⌝ ∗ state_interp_transient φ φt lr lrt lm lmt).
  Proof.
    iIntros (Hdom) "Htr".
    iDestruct (state_interp_transient_corr with "Htr") as "%HInv".
    destruct HInv as (lregs_t & lmem_t & cur_map & Hregs_incl & Hmem_incl & HInv).
    destruct (proj1 (elem_of_dom lrt r) Hdom) as (lrw & Hlrt).
    rewrite Hlrt.
    rewrite map_subseteq_spec in  Hregs_incl.
    specialize (Hregs_incl r lrw Hlrt).
    eapply state_corresponds_reg_get_word in Hregs_incl; eauto.
    erewrite Hregs_incl.
    iApply wp2_val. now iFrame.
  Qed.

  Lemma wp2_reg_lookup {lrt lmt r φ φt lr lm Φs Φf} :
    r ∈ dom lrt ->
    state_interp_transient φ φt lr lrt lm lmt ∗
      (∀ lwr, state_interp_transient φ φt lr lrt lm lmt -∗ Φs lwr (lword_get_word lwr)) ⊢
      wp_opt2 (lrt !! r) (reg φt !! r) Φf Φs.
  Proof.
    iIntros (Hdom) "[Htr Hk]".
    iPoseProof (wp2_reg_lookup2 Hdom with "Htr") as "Hwp".
    iApply (wp_opt2_mono with "[$Hwp Hk]").
    iIntros (lwr wr) "(-> & H)".
    now iApply "Hk".
  Qed.

  Lemma wp2_word_of_argument {src lw Φf Φs φ φt lr lrt lm lmt} :
    regs_of_argument src ⊆ dom lrt ->
    state_interp_transient φ φt lr lrt lm lmt ∗
      (∀ lw, state_interp_transient φ φt lr lrt lm lmt -∗ Φs lw (lword_get_word lw))
      ⊢ wp_opt2 (word_of_argumentL lrt src) (word_of_argument (reg φt) src) Φf Φs.
  Proof.
    iIntros (Hdom) "(Hσr & HΦs)".
    destruct src as [z|r]; cbn.
    - now iApply ("HΦs" with "Hσr").
    - iApply (wp2_reg_lookup (r := r) with "[$Hσr $HΦs]").
      now set_solver.
  Qed.

  Lemma wp2_addr_of_argument {src Φf Φs φ φt lr lrt lm lmt} :
    regs_of_argument src ⊆ dom lrt ->
    state_interp_transient φ φt lr lrt lm  lmt ∗
      (state_interp_transient φ φt lr lrt lm lmt -∗ Φf) ∧
      ((∀ z, state_interp_transient φ φt lr lrt lm lmt -∗ Φs z z))
      ⊢ wp_opt2 (addr_of_argumentL lrt src) (addr_of_argument (reg φt) src) Φf Φs.
  Proof.
    iIntros (Hregs) "(Hφ & Hk)".
    destruct src; cbn.
    - destruct (z_to_addr z); cbn; by iApply "Hk".
    - change (wp_opt2 _ _ _ _) with
        (wp_opt2
           ((lrt !! r ≫= fun y => match y with | LInt z => Some z | _ => None end)
              ≫= (λ n : Z, z_to_addr n))
          ((reg φt !! r ≫= fun y => match y with | WInt z => Some z | _ => None end)
              ≫= (λ n : Z, z_to_addr n))
           Φf Φs).
      rewrite <- wp_opt2_bind.
      rewrite <- wp_opt2_bind.
      iApply (wp2_reg_lookup with "[$Hφ Hk]").
      { set_solver. }
      iIntros (lwr) "Hφ".
      destruct lwr; cbn ; [destruct (z_to_addr z)| |] ; cbn; by iApply "Hk".
  Qed.

  Lemma wp2_otype_of_argument {src Φf Φs φ φt lr lrt lm lmt} :
    regs_of_argument src ⊆ dom lrt ->
    state_interp_transient φ φt lr lrt lm  lmt ∗
      (state_interp_transient φ φt lr lrt lm lmt -∗ Φf) ∧
      ((∀ z, state_interp_transient φ φt lr lrt lm lmt -∗ Φs z z))
      ⊢ wp_opt2 (otype_of_argumentL lrt src) (otype_of_argument (reg φt) src) Φf Φs.
  Proof.
    iIntros (Hregs) "(Hφ & Hk)".
    destruct src; cbn.
    - destruct (z_to_otype z); cbn; by iApply "Hk".
    - change (wp_opt2 _ _ _ _) with
        (wp_opt2
           ((lrt !! r ≫= fun y => match y with | LInt z => Some z | _ => None end)
              ≫= (λ n : Z, z_to_otype n))
          ((reg φt !! r ≫= fun y => match y with | WInt z => Some z | _ => None end)
              ≫= (λ n : Z, z_to_otype n))
           Φf Φs).
      rewrite <- wp_opt2_bind.
      rewrite <- wp_opt2_bind.
      iApply (wp2_reg_lookup with "[$Hφ Hk]").
      { set_solver. }
      iIntros (lwr) "Hφ".
      destruct lwr; cbn ; [destruct (z_to_otype z)| |] ; cbn; by iApply "Hk".
  Qed.

  Lemma wp2_word_get_cap {w Φf Φs} :
         Φf ∧ (∀ p b e a v, Φs (p , b , e , a , v) (p , b , e , a))
      ⊢ @wp_opt2 Σ _ _ (lword_get_cap w) (get_wcap (lword_get_word w)) Φf Φs.
  Proof.
    iIntros "HΦ".
    destruct w as [z | [p b e a v | x] | w]; cbn.
    all: try now rewrite bi.and_elim_l. all: try now rewrite bi.and_elim_r.
  Qed.

  Lemma wp2_mem_lookup {lrt lmt φ φt lr lm Φs Φf r p b e a v lwa} :
    withinBounds b e a = true ->
    lrt !! r = Some (LCap p b e a v) ->
    (snd <$> lmt) !! (a,v) = Some lwa ->
    state_interp_transient φ φt lr lrt lm lmt ∗
    (state_interp_transient φ φt lr lrt lm lmt -∗ Φs lwa (lword_get_word lwa)) ⊢
    wp_opt2 ((snd <$> lmt) !! (a,v)) (mem φt !! a) Φf Φs.
  Proof.
    iIntros (Hin_bounds Hlrt_r Hlmt_a) "(Hσr & Hk)".
    iPoseProof (state_interp_transient_corr with "Hσr") as "%Hcor".
    destruct Hcor as (lr' & lm' & cur_map & Hlrt_incl & Hlmt_incl & Hinv).
    rewrite Hlmt_a.
    eapply lookup_weaken in Hlmt_a, Hlrt_r; eauto.
    eapply state_corresponds_mem_get_word in Hlmt_a; eauto; cbn in Hlmt_a.
    2: { eapply state_corresponds_cap_cur_word; eauto; by cbn. }
    rewrite Hlmt_a.
    iApply wp2_val. now iApply "Hk".
  Qed.

  Lemma wp2_z_of_argument {src Φf Φs φ φt lr lrt lm lmt} :
    regs_of_argument src ⊆ dom lrt ->
    state_interp_transient φ φt lr lrt lm  lmt ∗
      (state_interp_transient φ φt lr lrt lm lmt -∗ Φf) ∧
      ((∀ z, state_interp_transient φ φt lr lrt lm lmt -∗ Φs z z))
      ⊢ wp_opt2 (z_of_argumentL lrt src) (z_of_argument (reg φt) src) Φf Φs.
  Proof.
    iIntros (Hregs) "(Hφ & Hk)".
    destruct src; cbn.
    - rewrite bi.and_elim_r. by iApply "Hk".
    - change (wp_opt2 _ _ _ _) with
        (wp_opt2 (lrt !! r ≫= fun y => match y with | LInt z => Some z | _ => None end)
           (reg φt !! r ≫= fun y => match y with | WInt z => Some z | _ => None end)
           Φf Φs).
      rewrite <-wp_opt2_bind.
      iApply (wp2_reg_lookup with "[$Hφ Hk]").
      { set_solver. }
      iIntros (lwr) "Hφ".
      destruct lwr; cbn.
      + rewrite bi.and_elim_r. by iApply "Hk".
      + rewrite bi.and_elim_l. by iApply "Hk".
      + rewrite bi.and_elim_l. by iApply "Hk".
  Qed.

  (* More expressive version of update_state_interp_from_reg_nomod.
     This is needed for operations that edit a current (in terms of version) word,
     requiring us to re-prove "currentness" of the edited word.
     Think e.g. shrinking the bounds of a capability read from a register. *)
  Lemma update_state_interp_from_regs_mod {σ dst lw2 lregs}:
    dst ∈ dom lregs ->
    (forall cur_map, is_cur_regs lregs cur_map -> is_cur_word lw2 cur_map) ->
    state_interp_logical σ ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y) ⊢
      |==> state_interp_logical (update_reg σ dst (lword_get_word lw2)) ∗
                ([∗ map] k↦y ∈ <[ dst := lw2 ]> lregs, k ↦ᵣ y).
  Proof.
    iIntros (Hdst Hcur) "(Hσ & Hregs)".
    iDestruct "Hσ" as (lr lm vmap tbl_cur tbl_prev tbl_all)
        "(Hr & Hm
         & -> & Htbl_cur & Htbl_prev & Htbl_all
         & HEC
         & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
         & %HLinv)"
    ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hregs_incl".
    iMod ((gen_heap_update_inSepM _ _ dst lw2) with "Hr Hregs") as "[Hr Hregs]"; eauto.
    { now apply elem_of_dom. }
    iModIntro. iFrame.
    iExists _,_,vmap,_,_,_; iFrame.
    iPureIntro.
    repeat (split ; first done).
    apply state_phys_log_corresponds_update_reg; try easy.
    eapply Hcur.
    eapply (is_cur_regs_mono Hregs_incl).
    now eapply (proj2 (proj1 HLinv)).
  Qed.

  (** Updates the transient state with a register update to dst that writes
      a word lw2 **)
  Lemma update_state_interp_transient_from_regs_mod {σ σt lr lrt lm lmt dst lw2}:
    dst ∈ dom lrt ->
    (forall cur_map, is_cur_regs lrt cur_map -> is_cur_word lw2 cur_map) ->
    state_interp_transient σ σt lr lrt lm lmt ⊢
      state_interp_transient
      σ (update_reg σt dst (lword_get_word lw2))
      lr (<[ dst := lw2 ]> lrt) lm lmt .
  Proof.
    iIntros (Hdom Hcur) ">(Hσ & Hregs & $)".
    iApply (update_state_interp_from_regs_mod Hdom Hcur with "[$Hσ $Hregs]").
  Qed.

  (* This lemma updates the state for operations where a current word is
     immediately moved (to another register). Since the word was not edited,
     and it was read from a register, it is obviously already "current" *)
  Lemma update_state_interp_from_reg_nomod {σ src dst lw regs}:
    dst ∈ dom regs ->
    regs !! src = Some lw ->
    state_interp_logical σ ∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ⊢
      |==> state_interp_logical (update_reg σ dst (lword_get_word lw)) ∗
                ([∗ map] k↦y ∈ <[ dst := lw ]> regs, k ↦ᵣ y).
  Proof.
    intros Hdst Hsrc.
    eapply update_state_interp_from_regs_mod; now eauto.
  Qed.

  Lemma update_state_interp_int {σ dst z regs}:
    dst ∈ dom regs ->
    state_interp_logical σ ∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ⊢
      |==> state_interp_logical (update_reg σ dst (WInt z)) ∗ ([∗ map] k↦y ∈ <[ dst := LWInt z ]> regs, k ↦ᵣ y).
  Proof.
    intros Hdst.
    eapply (update_state_interp_from_regs_mod (lw2 := LWInt z)); now eauto.
  Qed.

  (** Updates the transient state with a register update to dst that writes
      an int z **)
  Lemma update_state_interp_transient_int {σ σt lr lrt lm lmt dst z}:
    dst ∈ dom lrt ->
    state_interp_transient σ σt lr lrt lm lmt ⊢
      state_interp_transient σ (update_reg σt dst (WInt z))
      lr (<[ dst := LWInt z ]> lrt) lm lmt.
  Proof.
    intros Hdom.
    now apply (update_state_interp_transient_from_regs_mod (lw2 := LWInt z) Hdom).
  Qed.

  Lemma update_state_interp_from_cap_mod {σ dst lw2 lregs} {lmem : LMemF} {p b e a v r}:
    dst ∈ dom lregs ->

    lregs !! r = Some (LCap p b e a v) ->
    withinBounds b e a = true ->
    (snd <$> lmem) !! (a, v) = Some lw2 ->

    state_interp_logical σ
      ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y)
      ∗ ([∗ map] la↦dw ∈ lmem, la ↦ₐ{dw.1} dw.2)
      ⊢ |==>
          state_interp_logical (update_reg σ dst (lword_get_word lw2))
            ∗ ([∗ map] k↦y ∈ <[ dst := lw2 ]> lregs, k ↦ᵣ y)
            ∗ ([∗ map] la↦dw ∈ lmem, la ↦ₐ{dw.1} dw.2)
  .
  Proof.
    iIntros (Hdst Hr Hinbounds Ha) "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm vmap tbl_cur tbl_prev tbl_all)
        "(Hr & Hm
         & -> & Htbl_cur & Htbl_prev & Htbl_all
         & HEC
         & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
         & %HLinv)"
    ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iPoseProof (gen_heap_valid_inclSepM_general with "Hm Hmem") as "%Hlmem_incl".
    iMod ((gen_heap_update_inSepM _ _ dst lw2) with "Hr Hregs") as "[Hr Hregs]"; eauto.
    { now apply elem_of_dom. }
    iModIntro. iFrame.
    iExists _,_,vmap,_,_,_; iFrame.
    iPureIntro.
    repeat (split ; first done).
    eapply lookup_weaken in Ha ; eauto.
    apply state_phys_log_corresponds_update_reg; try easy.
    destruct HLinv as [Hinv_reg Hinv_mem].
    eapply lmem_corresponds_read_iscur; eauto.
    eapply lookup_weaken in Hr ; eauto.
    eapply state_corresponds_cap_cur_word ; eauto; by cbn.
  Qed.

  (** Updates the transient state with a register update to dst that writes
      a value lw retrieved from memory using the capability in r **)
  Lemma update_state_interp_transient_from_cap_mod
    {σ σt lr lrt lm lmt dst lw2 r p b e a v}:
    dst ∈ dom lrt ->
    lrt !! r = Some (LCap p b e a v) ->
    withinBounds b e a = true ->
    (snd <$> lmt) !! (a, v) = Some lw2 ->
    state_interp_transient σ σt lr lrt lm lmt ⊢
      state_interp_transient
      σ (update_reg σt dst (lword_get_word lw2))
      lr (<[ dst := lw2 ]> lrt) lm lmt.
  Proof.
    iIntros (Hdom Hr Hinbounds Ha) ">(Hσ & Hregs & Hmem)".
    now iApply (update_state_interp_from_cap_mod Hdom Hr Hinbounds Ha with "[$Hσ $Hregs $Hmem]").
  Qed.

  Lemma update_state_interp_from_mem_mod {σ lregs} {lmem : LMemF} laddr lwold lwnew :
    (forall cur_map, is_cur_regs lregs cur_map -> is_cur_word lwnew cur_map) ->
    (forall cur_map, is_cur_regs lregs cur_map -> is_cur_addr laddr cur_map) ->
    lmem !! laddr = Some (DfracOwn 1, lwold) ->

    state_interp_logical σ
      ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y)
      ∗ ([∗ map] la↦dw ∈ lmem, la ↦ₐ{dw.1} dw.2)
      ⊢ |==>
          state_interp_logical (update_mem σ (laddr_get_addr laddr) (lword_get_word lwnew))
            ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y)
            ∗ ([∗ map] la↦dw ∈ <[laddr := (DfracOwn 1, lwnew) ]> lmem, la ↦ₐ{dw.1} dw.2).
  Proof.
    iIntros (Hcurw Hcura Hladdr) "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm vmap tbl_cur tbl_prev tbl_all)
        "(Hr & Hm
         & -> & Htbl_cur & Htbl_prev & Htbl_all
         & HEC
         & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
         & %HLinv)"
    ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iPoseProof (gen_heap_valid_inclSepM_general with "Hm Hmem") as "%Hlmem_incl".
    iFrame.
    iMod ((gen_heap_update_inSepM_general _ _ laddr lwnew) with "Hm Hmem") as "[Hm Hmem]"; eauto.
    iModIntro. iFrame.
    iExists _,_,vmap,_,_,_; iFrame.
    iPureIntro.
    repeat (split ; first done).
    destruct HLinv as [[? Hregscur] Hinv_mem].
    apply state_phys_log_corresponds_update_mem; try easy.
    1: apply Hcura.
    2: apply Hcurw.
    all: apply (is_cur_regs_mono Hlregs_incl); auto.
Qed.

  (** Updates the transient state with a memory update to address la, writing
      a word lw **)
  Lemma update_state_interp_transient_from_mem_mod {σ σt lr lrt} {lm lmt : LMemF} la lw lw' :
    (forall cur_map, is_cur_regs lrt cur_map -> is_cur_word lw cur_map) ->
    (forall cur_map, is_cur_regs lrt cur_map -> is_cur_addr la cur_map) ->
    lmt !! la = Some (DfracOwn 1, lw') ->
    state_interp_transient σ σt lr lrt lm lmt ⊢
    state_interp_transient σ (update_mem σt (laddr_get_addr la) (lword_get_word lw))
                          lr lrt (* registers remain unchanged *)
                          lm (<[ la := (DfracOwn 1, lw)]> lmt).
  Proof.
    iIntros (Hcurw Hcura Hla) ">Hσ".
    now iApply (update_state_interp_from_mem_mod la lw' lw Hcurw Hcura Hla).
  Qed.


  Lemma wp2_opt_incrementPC2 {lregs σr σm lmem vmap lrt} :
    PC ∈ dom lrt ->
    lrt ⊆ lregs ->
    state_phys_log_corresponds σr σm lregs lmem vmap ->
    gen_heap_interp lregs ∗ ([∗ map] k↦y ∈ lrt, k ↦ᵣ y)
      ⊢ wp_opt2 (incrementLPC lrt) (incrementPC σr) (gen_heap_interp lregs ∗ ([∗ map] k↦y ∈ lrt, k ↦ᵣ y))
      (fun lrt2 rs2 => ∃ lregs2, gen_heap_interp lregs2 ∗ ⌜state_phys_log_corresponds rs2 σm lregs2 lmem vmap⌝ ∗
                                   ([∗ map] k↦y ∈ lrt2, k ↦ᵣ y)).
  Proof.
    iIntros (Hdom Hlrt Hcorr) "(Hσr & Hregs)".
    iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    iApply wp_opt2_mono2.
    iSplitL; last by iApply wp2_reg_lookup5.
    iSplit; first by iIntros "%f".
    iIntros (lw w) "-> %Heq1 %Heq2".
    destruct lw; cbn; try by iFrame.
    destruct sb; cbn; try by iFrame.
    destruct (f1 + 1)%a; cbn; try by iFrame.
    iMod ((gen_heap_update_inSepM _ _ PC (LCap p f f0 f2 v)) with "Hσr Hregs") as "[Hr Hregs]"; eauto.
    iExists _. iFrame.
    iPureIntro.
    eapply state_phys_log_corresponds_update_reg; try easy.
    eapply is_cur_lword_lea with (lw := LCap p f f0 f1 v); try now cbn.
    { apply isWithin_refl. }
    refine (is_cur_regs_mono Hlrt _ PC _ _); last easy.
    now destruct Hcorr as [[_ Hcurregs] _].
  Qed.

  Lemma wp2_opt_incrementPC {φ φt lr lrt lm lmt Φs Φf} :
    PC ∈ dom lrt ->
    state_interp_transient φ φt lr lrt lm lmt ∗
      ((state_interp_transient φ φt lr lrt lm lmt -∗ Φf) ∧
         (∀ lrt' rs',
            state_interp_transient φ (update_regs φt rs') lr lrt' lm lmt -∗ Φs lrt' rs'))
      ⊢ wp_opt2 (incrementLPC lrt) (incrementPC (reg φt)) Φf Φs.
  Proof.
    iIntros (Hdom) "(Hφr & Hk)".
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn.
    iApply (wp2_reg_lookup with "[$Hφr Hk]"); first done.

    iIntros (lwr) "Hφr %Heq1 %Heq2".
    destruct lwr; cbn;
      try (rewrite bi.and_elim_l; now iApply "Hk").
    destruct sb; cbn;
      try (rewrite bi.and_elim_l; now iApply "Hk").
    destruct (f1 + 1)%a; cbn;
      try (rewrite bi.and_elim_l; now iApply "Hk").
    rewrite bi.and_elim_r.
    iApply ("Hk" $! _ (<[PC := _ ]> (reg φt))).
    iApply (update_state_interp_transient_from_regs_mod Hdom (lw2 := LCap p f f0 f2 v) with "Hφr").

    intros cur_map Hcurregs.
    eapply is_cur_lword_lea with (lw := LCap p f f0 f1 v); try now cbn.
    apply isWithin_refl.
    by eapply (map_Forall_lookup_1 _ _ _ _ Hcurregs).
  Qed.

  Lemma wp2_get_wcap_scap {Φf : iProp Σ} {w Φs} :
         Φf ∧ (∀ p b e a v, Φs (p, b, e, a, v) (p, b, e, a))
      ⊢ wp_opt2 (get_wlcap_slcap w) (get_wcap_scap (lword_get_word w)) Φf Φs.
  Proof.
    iIntros "HΦ".
    destruct w as [ | [ | ] | [] [ | ] ]; cbn.
    all: try now rewrite bi.and_elim_l.
    all: try now rewrite bi.and_elim_r.
  Qed.

  Lemma state_interp_transient_unique_in_lregs
    {σ σt lreg lrt lmemf lmt src lwsrc}:
    sweep_reg (mem σ) (reg σ) src = true ->
    lreg !! src = Some lwsrc ->
    state_interp_transient σ σt lreg lrt lmemf lmt ⊢
    ⌜ unique_in_registersL lreg (Some src) lwsrc ⌝.
  Proof.
    iIntros (Hsweep Hsrc) "Hσrm".
    iDestruct (transiently_abort with "Hσrm") as "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm vmap cur_tb prev_tb all_tb) "(Hr & Hm & %Hcurtbeq & Hcurtb & Hprevtb & Halltb & Hecauth & %Hcurprevdisj & %Hcompl & %Hcurprevdisj2 & %Hcompl2 & %HLinv)"; simpl in HLinv.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hregs_incl".
    iPureIntro.
    eapply unique_in_registersL_mono; first done.
    eapply lookup_weaken in Hsrc; eauto.
    eapply state_corresponds_unique_in_registers; eauto.
    eapply (sweep_reg_spec _ _ _ _ Hsweep) ; cbn.
    eapply state_corresponds_reg_get_word; eauto.
    eapply state_corresponds_reg_get_word; eauto.
  Qed.

  (* Lemma state_interp_derive (E : coPset) (s : stuckness) (R P : iProp Σ) (HPers : Persistent P) Φ e : *)
  (*   to_val e = None -> *)
  (*   (∀ σ, R ∗ state_interp_logical σ -∗ P) -∗ *)
  (*   (R ∗ P -∗ (wp s E e Φ)) -∗ *)
  (*   (R -∗ (wp s E e Φ)). *)
  (* Proof. *)
  (*   iIntros (He) "HRP Hwp HR". *)
  (*   rewrite !wp_unfold /wp_pre /=. *)
  (*   rewrite He. *)
  (*   iIntros (σ ns κ κs nt) "Hσ /=". *)
  (*   iDestruct ("HRP" with "[$HR $Hσ]") as "#HP". *)
  (*   iDestruct ("Hwp" with "[$HR $HP]") as "Hwp". *)
  (*   iSpecialize ("Hwp" $! σ ns κ κs nt with "Hσ"). *)
  (*   iMod ("Hwp") as "[%Hred H]". *)
  (*   iModIntro. iSplitR; first by iPureIntro. *)
  (*   iIntros (? ? ?) "%Hstep Hcred". *)
  (*   iMod ("H" $! e2 σ2 efs Hstep with "Hcred") as "H". *)
  (*   done. *)
  (* Qed. *)

  (* Lemma ec_bounds_etable σ `{ReservedAddresses} `{!ceriseG Σ} : *)
  (*   state_interp_logical σ -∗ *)
  (*   ⌜forall i, i ∈ dom σ.(etable) → i < σ.(enumcur)⌝. *)
  (* Proof. *)
  (*   iIntros "σ". *)
  (*   iDestruct "σ" as (lr lm vm cur_tb prev_tb all_tb) *)
  (*                      "(Hlr & Hlm & %Hetable & Hcur_tb & Hprev_tb & Hall_tb & Hecauth & %Hdomcurtb & %Hdomtbcompl & %Htbdisj & %Htbcompl & %Hcorr0)". *)
  (*   iPureIntro. *)
  (*   intros i Hdom. *)
  (*   rewrite -Hetable in Hdom. *)
  (*   apply (elem_of_weaken i (dom cur_tb) (dom (cur_tb ∪ prev_tb))) in Hdom. *)
  (*   rewrite list_to_set_seq in Hdomtbcompl. *)
  (*   set_solver. *)
  (*   set_solver. *)
  (* Qed. *)

  (* Lemma state_interp_derive_instr_exec (E : coPset) (s : stuckness) (R P : iProp Σ) (HPers : Persistent P) Φ : *)
  (*   (∀ σ, R ∗ state_interp_logical σ -∗ P) -∗ *)
  (*   (R ∗ P -∗ (wp s E (Instr Executable) Φ)) -∗ *)
  (*   (R -∗ wp s E (Instr Executable) Φ). *)
  (* Proof. *)
  (*   iIntros "HRP Hwp HR". *)
  (*   by iApply (state_interp_derive with "[$HRP] [$Hwp] [$HR]"). *)
  (* Qed. *)

  (* Lemma state_interp_max_tidx σ ecn tidx I : *)
  (*   state_interp_logical σ -∗ *)
  (*   EC⤇ ecn -∗ *)
  (*   enclave_all tidx I -∗ *)
  (*   ⌜ tidx < ecn ⌝. *)
  (* Proof. *)
  (*   iIntros "Hinterp HEC Henclave". *)
  (*   iDestruct (ec_bounds_etable with "Hinterp") as "%Hbound". *)
  (*   iDestruct "Hinterp" as (lr lm vm cur_tb prev_tb all_tb) *)
  (*                            "(Hlr & Hlm & %Hetable & Hcur_tb & Hprev_tb & Hall_tb & Hecauth & %Hdomcurtb & %Hdomtbcompl & %Htbdisj & %Htbcompl & %Hcorr0)". *)
  (*   iCombine "Hecauth HEC" as "Henumcur". *)
  (*   iDestruct (own_valid with "Henumcur") as "%Hvalid_ec". *)
  (*   apply excl_auth_agree_L in Hvalid_ec. *)
  (*   rewrite -Hvalid_ec. *)
  (*   iAssert (⌜tidx ∈ dom all_tb⌝%I) as "%Hin". *)
  (*   iCombine "Hall_tb" "Henclave" as "Hall". *)
  (*   iDestruct (own_valid with "Hall") as "%Hvalid_all". *)
  (*   apply auth_both_valid_discrete in Hvalid_all as [Hlt_all Hvalid_all]. *)
  (*   apply gmap.dom_included in Hlt_all. *)
  (*   by rewrite dom_singleton dom_fmap singleton_subseteq_l in Hlt_all. *)
  (*   rewrite -Htbcompl in Hin. *)
  (*   iPureIntro. *)
  (*   rewrite Hdomtbcompl in Hin. *)
  (*   rewrite list_to_set_seq in Hin. *)
  (*   set_solver +Hin. *)
  (* Qed. *)

  (* Lemma valid_enclave_ec ecn tidx I s E Φ : *)
  (*   ( ( EC⤇ ecn ∗ enclave_all tidx I) ∗ ⌜ tidx < ecn ⌝ -∗ (wp s E (Instr Executable) Φ)) ⊢ *)
  (*   ( ( EC⤇ ecn ∗ enclave_all tidx I) -∗ wp s E (Instr Executable) Φ). *)
  (* Proof. *)
  (*   iIntros "Hwp HR". *)
  (*   iApply (state_interp_derive_instr_exec with "[] [$Hwp] [$HR]"). *)
  (*   iIntros (σ) "( (HEC & Henclave) & Hσ)". *)
  (*   iApply (state_interp_max_tidx with "[$] [$] [$]"). *)
  (* Qed. *)

  Definition full_own_mem (lmem : LMem) : LMemF := (λ y : LWord, (DfracOwn 1, y)) <$> lmem.

  (* TODO generalise and move *)
  Lemma fmap_forall_inv (lmt : LMemF) :
    map_Forall (λ (_ : LAddr) (a : dfrac * LWord), a.1 = DfracOwn 1) lmt ->
    exists lm, lmt = (full_own_mem lm).
  Proof.
    induction lmt using map_ind; intro Hall.
    - exists ∅. by rewrite /full_own_mem fmap_empty.
    - assert (x.1 = DfracOwn 1) as Hx by (apply map_Forall_insert_1_1 in Hall; auto).
      apply map_Forall_insert_1_2 in Hall; auto.
      apply IHlmt in Hall.
      destruct Hall as (lm' & Hall).
      exists (<[i := (snd x)]> lm').
      rewrite /full_own_mem fmap_insert /=.
      by destruct x ; cbn in * ; subst.
  Qed.


  (* TODO generalise to not just LMem + find better name + move iris_extra *)
  Lemma map_full_own (lm : LMem) :
    ([∗ map] k↦y ∈ lm, k ↦ₐ y)%I
    ⊣⊢ ([∗ map] la↦dw ∈ (full_own_mem lm), la ↦ₐ{dw.1} dw.2).
  Proof.
    induction lm using map_ind.
    - rewrite /full_own_mem fmap_empty.
      by iSplit; iIntros "Hmem".
    - rewrite /full_own_mem fmap_insert.
      iSplit; iIntros "Hmem".
      + iDestruct (big_sepM_insert with "Hmem") as "[Hi Hmem]"; first done.
        iDestruct (IHlm with "Hmem") as "Hmem".
        iDestruct (big_sepM_insert with "[Hi Hmem]") as "Hmem"; try iFrame.
        by rewrite lookup_fmap fmap_None.
        by cbn.
      + iDestruct (big_sepM_insert with "Hmem") as "[Hi Hmem]"
        ; first (by rewrite lookup_fmap fmap_None).
        iDestruct (IHlm with "Hmem") as "Hmem".
        cbn.
        by iDestruct (big_sepM_insert with "[Hi Hmem]") as "Hmem"; try iFrame.
  Qed.

  Lemma update_state_interp_next_version
    {σr σm lr lm vmap lregs lmem src lwsrc p b e a v} :

    let la := finz.seq_between b e in
    la ## reserved_addresses ->
    sweep_reg σm σr src = true ->
    lregs !! src = Some lwsrc ->
    get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
    gen_heap_interp lr ∗ gen_heap_interp lm ∗
      ⌜state_phys_log_corresponds σr σm lr lm vmap⌝%I
      ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ full_own_mem lmem, k ↦ₐ{y.1} y.2)
      ⊢ |==>
      let lmem' := update_version_region lm la v lmem in
      let lm' := update_version_region lm la v lm in
      let lregs' := (<[src:=next_version_lword lwsrc]> lregs) in
      let lr' := (<[src:=next_version_lword lwsrc]> lr) in
      let vmap' := update_version_region_vmap la v vmap in
      ⌜ is_valid_updated_lmemory lm lmem (finz.seq_between b e) v lmem'⌝ ∗
        gen_heap_interp lr' ∗ gen_heap_interp lm' ∗
        ⌜state_phys_log_corresponds σr σm lr' lm' vmap' ⌝%I ∗ ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ full_own_mem lmem', k ↦ₐ{y.1} y.2).
  Proof.
    iIntros (la Hnotres' Hsweep Hlsrc Hlcap_wsrc) "(Hr & Hm & %Hcorr & Hregs & Hmem)".
    assert (Forall (λ a0 : Addr, a0 ∉ reserved_addresses) la) as Notres.
    {
      rewrite Forall_forall ; intros x Hx Hx'.
      eapply Hnotres'; eauto.
    }
    iDestruct (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iDestruct (map_full_own with "Hmem") as "Hmem".
    iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as "%Hlmem_incl".
    iMod ((gen_heap_update_inSepM _ _ src (next_version_lword lwsrc)) with "Hr Hregs") as
      "[Hr Hregs]"; eauto.
    assert (lr !! src = Some lwsrc) as Hsrc by (eapply lookup_weaken in Hlsrc ; eauto).
    assert (HNoDup : NoDup (finz.seq_between b e)) by (apply finz_seq_between_NoDup).
    opose proof
      (state_corresponds_cap_all_current _ _ _ _ _ _ _ _ _ _ _ _ Hcorr _ Hsrc)
      as HcurMap ; first (by cbn).
    opose proof
      (state_corresponds_last_version_lword_region _ _ _ _ _ _ _ _ _ _ _ _  Hcorr _ Hsrc)
      as HmemMap_maxv; first (by cbn).
    opose proof
      (state_corresponds_access_lword_region _ _ _ _ _ _ _ _ _ _ _ _ Hcorr _ Hsrc)
      as HmemMap; first (by cbn).
    set (lmem' := update_version_region lm la v lmem).
    set (lm' := update_version_region lm la v lm).
    set (lregs' := <[src:=next_version_lword lwsrc]> lregs).
    set (lr' := <[src:=next_version_lword lwsrc]> lr).
    set (vmap' := update_version_region_vmap la v vmap).
    iMod ((gen_heap_lmem_version_update lm lmem lm lmem' _ vmap _ (finz.seq_between b e) v)
           with "Hm Hmem") as "[Hm Hmem]"; eauto.
    iModIntro.
    iSplitR.
    { iPureIntro. now apply is_valid_updated_lmemory_update_version_region. }
    iFrame.
    iSplitR "Hmem"; last by rewrite map_full_own.
    iPureIntro.
    assert (lr !! src = Some lwsrc) as Hsrc' by (eapply lookup_weaken; eauto).
    eapply sweep_true_specL in Hsweep; eauto.
    split.
    + rewrite (_: σr = (<[src:=(lword_get_word (next_version_lword lwsrc))]> σr)).
      * eapply update_version_region_lreg_corresponds_src; eauto.
        eapply update_version_word_region_update_lword; eauto.
        eapply lreg_corresponds_read_iscur; eauto.
        by destruct Hcorr.
      * rewrite lword_get_word_next_version.
        rewrite insert_id; first done.
        eapply state_corresponds_reg_get_word; eauto.
    + destruct (id Hcorr).
      eapply update_version_region_preserves_mem_corresponds; eauto.
      destruct (Hsweep Hsrc').
      eapply unique_in_machine_no_accessL; eauto.
      eapply lreg_corresponds_read_iscur; eauto.
  Qed.

End cap_lang_rules.
