From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode spec_patterns coq_tactics ltac_tactics reduction.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel.
From cap_machine Require Export iris_extra addr_reg_sample contiguous malloc assert.
From cap_machine Require Import map_simpl.
From cap_machine.proofmode Require Import classes tactics_helpers solve_pure proofmode.


Section macros.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {seals:sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- FETCH ------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition fetch_instrs (f : Z) : list LWord :=
    encodeInstrsLW [
      Mov r_t1 PC;
      GetB r_t2 r_t1;
      GetA r_t3 r_t1;
      Sub r_t2 r_t2 r_t3;
      Lea r_t1 r_t2;
      Load r_t1 r_t1;
      Lea r_t1 f;
      Mov r_t2 0;
      Mov r_t3 0;
      Load r_t1 r_t1
    ].

  Lemma fetch_spec f pc_p pc_b pc_e pc_v a_first b_link e_link a_link v_link entry_a wentry φ w1 w2 w3:
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (fetch_instrs f))%a →
    withinBounds b_link e_link entry_a = true ->
    (a_link + f)%a = Some entry_a ->

      ▷ codefrag a_first pc_v (fetch_instrs f)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
    ∗ ▷ (entry_a,v_link) ↦ₐ wentry
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (fetch_instrs f))%a pc_v
         ∗ codefrag a_first pc_v (fetch_instrs f)
         (* the newly allocated region *)
         ∗ r_t1 ↦ᵣ wentry ∗ r_t2 ↦ᵣ LInt 0%Z ∗ r_t3 ↦ᵣ LInt 0%Z
         ∗ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
         ∗ (entry_a,v_link) ↦ₐ wentry
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Hentry) "(>Hprog & >HPC & >Hpc_b & >Ha_entry & >Hr_t1 & >Hr_t2 & >Hr_t3 & Hφ)".
    codefrag_facts "Hprog".
    iGo "Hprog". transitivity (Some pc_b); eauto. solve_addr.
    iGo "Hprog". iApply "Hφ"; iFrame.
 Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------------------------------- FETCH BIS ----------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition fetch_reg_instrs (f : Z) (r_lt : RegName): list LWord :=
    (* r_lt := (RO, b_lt, e_lt, b_tbl) ; linking table capability *)
    encodeInstrsLW [
        Lea r_lt f; (* r_lt := (RO, b_lt, e_lt, b_tbl + f) *)
        Load r_lt r_lt (* r_lt := mem(b_tbl + f) *)
      ].

  Lemma fetch_reg_spec f r_lt pc_p pc_b pc_e pc_v a_first b_link e_link a_link v_link entry_a wentry φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (fetch_reg_instrs f r_lt))%a →
    withinBounds b_link e_link entry_a = true ->
    (a_link + f)%a = Some entry_a ->

      ▷ codefrag a_first pc_v (fetch_reg_instrs f r_lt)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ (entry_a,v_link) ↦ₐ wentry
    ∗ ▷ r_lt ↦ᵣ LCap RO b_link e_link a_link v_link
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (fetch_reg_instrs f r_lt))%a pc_v
         ∗ codefrag a_first pc_v (fetch_reg_instrs f r_lt)
         (* the newly allocated region *)
         ∗ r_lt ↦ᵣ wentry
         ∗ (entry_a,v_link) ↦ₐ wentry
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Hentry) "(>Hprog & >HPC & >Ha_entry & >Hr_t1 & Hφ)".
    codefrag_facts "Hprog".
    iGo "Hprog".
    iApply "Hφ"; iFrame.
 Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- ASSERT ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  Definition assert_instrs f_a :=
    fetch_instrs f_a ++
    encodeInstrsLW [
      Mov r_t2 r_t0;
      Mov r_t0 PC;
      Lea r_t0 3;
      Jmp r_t1;
      Mov r_t0 r_t2;
      Mov r_t1 0;
      Mov r_t2 0
    ].

  (* Spec for assertion success *)
  Lemma assert_success f_a pc_p pc_b pc_e pc_v a_first
        b_link e_link a_link v_link a_entry ba a_flag ea v_assert w0 w1 w2 w3 assertN EN n1 n2 φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (assert_instrs f_a))%a →
    (* linking table assumptions *)
    withinBounds b_link e_link a_entry = true →
    (a_link + f_a)%a = Some a_entry ->
    ↑assertN ⊆ EN →
    (* condition for assertion success *)
    (n1 = n2) →

    ▷ codefrag a_first pc_v (assert_instrs f_a)
    ∗ na_inv logrel_nais assertN (assert_inv ba a_flag ea v_assert)
    ∗ na_own logrel_nais EN
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
    ∗ ▷ (a_entry,v_link) ↦ₐ LCap E ba ea ba v_assert
    ∗ ▷ r_t0 ↦ᵣ w0
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ r_t4 ↦ᵣ LInt n1
    ∗ ▷ r_t5 ↦ᵣ LInt n2
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (assert_instrs f_a))%a pc_v
         ∗ r_t0 ↦ᵣ w0
         ∗ r_t1 ↦ᵣ LInt 0%Z ∗ r_t2 ↦ᵣ LInt 0%Z ∗ r_t3 ↦ᵣ LInt 0%Z
         ∗ r_t4 ↦ᵣ LInt 0%Z ∗ r_t5 ↦ᵣ LInt 0%Z
         ∗ codefrag a_first pc_v (assert_instrs f_a)
         ∗ na_own logrel_nais EN
         ∗ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
         ∗ (a_entry,v_link) ↦ₐ LCap E ba ea ba v_assert
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Htable HN Hsuccess)
            "(>Hprog & #Hinv & Hna & >HPC & >Hpc_b & >Ha_entry & >Hr0 & >Hr1 & >Hr2 & >Hr3
              & >Hr4 & >Hr5 & Hφ)".
    rewrite {1}/assert_instrs.
    focus_block_0 "Hprog" as "Hfetch" "Hcont".
    iApply fetch_spec; iFrameAutoSolve.
    iNext. iIntros "(HPC & Hfetch & Hr1 & Hr2 & Hr3 & Hpc_b & Ha_entry)".
    unfocus_block "Hfetch" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    do 4 iInstr "Hprog".
    iApply (assert_success_spec with "[- $Hinv $Hna $HPC $Hr0 $Hr4 $Hr5]"); auto.
    iNext. iIntros "(Hna & HPC & Hr0 & Hr4 & Hr5)".
    rewrite updatePcPermL_cap_non_E; [| solve_pure ].
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ". iFrame.
    changePCto (a_first ^+ length (assert_instrs f_a))%a. iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------------------------------- ASSERT BIS ---------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition assert_reg_instrs f_a r_lt :=
    fetch_reg_instrs f_a r_lt ++
    encodeInstrsLW [
      Mov r_t2 r_t0;
      Mov r_t0 PC;
      Lea r_t0 3;
      Jmp r_lt;
      Mov r_t0 r_t2;
      Mov r_lt 0;
      Mov r_t2 0
    ].

  (* Spec for assertion success *)
  Lemma assert_reg_success f_a r_lt pc_p pc_b pc_e pc_v a_first
        b_link e_link a_link v_link a_entry ba a_flag ea v_assert w0 w2 assertN EN n1 n2 φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (assert_reg_instrs f_a r_lt))%a →
    (* linking table assumptions *)
    withinBounds b_link e_link a_entry = true →
    (a_link + f_a)%a = Some a_entry ->
    ↑assertN ⊆ EN →
    (* condition for assertion success *)
    (n1 = n2) →

    ▷ codefrag a_first pc_v (assert_reg_instrs f_a r_lt)
    ∗ na_inv logrel_nais assertN (assert_inv ba a_flag ea v_assert)
    ∗ na_own logrel_nais EN
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ (a_entry,v_link) ↦ₐ LCap E ba ea ba v_assert
    ∗ ▷ r_t0 ↦ᵣ w0
    ∗ ▷ r_lt ↦ᵣ (LCap RO b_link e_link a_link v_link)
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t4 ↦ᵣ LInt n1
    ∗ ▷ r_t5 ↦ᵣ LInt n2
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (assert_reg_instrs f_a r_lt))%a pc_v
         ∗ r_t0 ↦ᵣ w0
         ∗ r_lt ↦ᵣ LInt 0%Z ∗ r_t2 ↦ᵣ LInt 0%Z
         ∗ r_t4 ↦ᵣ LInt 0%Z ∗ r_t5 ↦ᵣ LInt 0%Z
         ∗ codefrag a_first pc_v (assert_reg_instrs f_a r_lt)
         ∗ na_own logrel_nais EN
         ∗ (a_entry,v_link) ↦ₐ LCap E ba ea ba v_assert
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Htable HN Hsuccess)
            "(>Hprog & #Hinv & Hna & >HPC & >Ha_entry & >Hr0 & >Hrlt & >Hr2
              & >Hr4 & >Hr5 & Hφ)".
    rewrite {1}/assert_reg_instrs.
    focus_block_0 "Hprog" as "Hfetch" "Hcont".
    iApply fetch_reg_spec; iFrameAutoSolve.
    iNext. iIntros "(HPC & Hfetch & Hrlt & Hpc_b & Ha_entry)".
    unfocus_block "Hfetch" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    do 4 iInstr "Hprog".
    iApply (assert_success_spec with "[- $Hinv $Hna $HPC $Hr0 $Hr4 $Hr5]"); auto.
    iNext. iIntros "(Hna & HPC & Hr0 & Hr4 & Hr5)".
    rewrite updatePcPermL_cap_non_E; [| solve_pure ].
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ". iFrame.
    changePCto (a_first ^+ length (assert_reg_instrs f_a r_lt))%a. iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- MALLOC ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* malloc stores the result in r_t1, rather than a user chosen destination.
     f_m is the offset of the malloc capability *)
  Definition malloc_instrs f_m (size: Z) :=
    fetch_instrs f_m ++
    encodeInstrsLW [
     Mov r_t5 r_t0;
     Mov r_t3 r_t1;
     Mov r_t1 size;
     Mov r_t0 PC;
     Lea r_t0 3;
     Jmp r_t3;
     Mov r_t0 r_t5;
     Mov r_t5 0
  ].

  (* malloc spec *)
  Lemma malloc_spec_alt φ ψ size cont pc_p pc_b pc_e pc_v a_first
        b_link e_link a_link v_link f_m a_entry v_malloc mallocN b_m e_m EN rmap :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (malloc_instrs f_m size))%a →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    (size > 0)%Z →

    (* malloc program and subroutine *)
    ▷ codefrag a_first pc_v (malloc_instrs f_m size)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m v_malloc)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
    ∗ ▷ (a_entry,v_link) ↦ₐ LCap E b_m e_m b_m v_malloc
    (* register state *)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* failure/continuation *)
    ∗ ▷ (∀ v, ψ v -∗ φ v)
    ∗ ▷ (φ FailedV)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (malloc_instrs f_m size))%a pc_v
         ∗ codefrag a_first pc_v (malloc_instrs f_m size)
         ∗ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
         ∗ (a_entry,v_link) ↦ₐ LCap E b_m e_m b_m v_malloc
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ LCap RWX b e b v_malloc
            ∗ [[b,e]] ↦ₐ{v_malloc} [[region_addrs_zeroesL b e v_malloc]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=LInt 0%Z]>
                               (<[r_t3:=LInt 0%Z]>
                                (<[r_t4:=LInt 0%Z]>
                                 (<[r_t5:=LInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *)
         -∗ WP Seq (Instr Executable) {{ ψ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hψ & Hφfailed & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! r_t1)) as [rv1 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t2)) as [rv2 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! r_t3)) as [rv3 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (rmap !! r_t5)) as [rv5 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]". by rewrite !lookup_delete_ne //.

    rewrite {1}/malloc_instrs.
    focus_block_0 "Hprog" as "Hfetch" "Hcont".
    iApply fetch_spec; iFrameAutoSolve.
    iNext. iIntros "(HPC & Hfetch & Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    unfocus_block "Hfetch" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as amid1 Hamid1 "Hprog" "Hcont".
    iGo "Hprog". (* PC is now at b_m *)
    (* we are now ready to use the malloc subroutine spec. For this we prepare the registers *)
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      by simplify_map_eq.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs".
      by simplify_map_eq.
    map_simpl "Hregs".
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
      by simplify_map_eq.
    map_simpl "Hregs".
    iApply (wp_wand with "[- Hφfailed Hψ]").
    iApply (simple_malloc_subroutine_spec with "[- $Hmalloc $Hna $Hregs $Hr_t0 $HPC $Hr_t1]"); auto.
    { set_solver+ Hrmap_dom. }
    iNext.
    rewrite updatePcPermL_cap_non_E; [| solve_pure].
    iIntros "((Hna & Hregs) & Hr_t0 & HPC & Hbe) /=".
    iDestruct "Hbe" as (b e size' Hsize' Hbe) "(Hr_t1 & Hbe)". inversion Hsize'; subst size'.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]".
      simplify_map_eq. eauto.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]".
      simplify_map_eq. eauto.
    (* back our program, in the continuation of malloc *)
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    (* continuation *)
    iApply "Hφ". changePCto (a_first ^+ 18%nat)%a.
    iFrame. iSplitL "Hr_t1 Hbe".
    { iExists _,_. iFrame. iPureIntro; eauto. }
    { iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
        simplify_map_eq. reflexivity.
      iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      simplify_map_eq. reflexivity.
      iFrameMapSolve+ Hrmap_dom "Hregs". }
    { iIntros (w) "[Hφ|Hφ] /=". iApply "Hψ". iFrame. iSimplifyEq. eauto. }
  Qed.

  (* malloc spec - alternative formulation *)
  Lemma malloc_spec φ size cont pc_p pc_b pc_e pc_v a_first
        b_link e_link a_link v_link f_m a_entry v_malloc mallocN b_m e_m EN rmap :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (malloc_instrs f_m size))%a →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    (size > 0)%Z →

    (* malloc program and subroutine *)
    ▷ codefrag a_first pc_v (malloc_instrs f_m size)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m v_malloc)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
    ∗ ▷ (a_entry,v_link) ↦ₐ LCap E b_m e_m b_m v_malloc
    (* register state *)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (malloc_instrs f_m size))%a pc_v
         ∗ codefrag a_first pc_v (malloc_instrs f_m size)
         ∗ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
         ∗ (a_entry,v_link) ↦ₐ LCap E b_m e_m b_m v_malloc
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ LCap RWX b e b v_malloc
            ∗ [[b,e]] ↦ₐ{v_malloc} [[region_addrs_zeroesL b e v_malloc]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=LInt 0%Z]>
                               (<[r_t3:=LInt 0%Z]>
                                (<[r_t4:=LInt 0%Z]>
                                 (<[r_t5:=LInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *)
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hφ)".
    iApply malloc_spec_alt; iFrameAutoSolve; eauto. iFrame. iFrame "Hmalloc".
    iSplitL. iNext. eauto. eauto.
  Qed.

  (* ------------------------------- *)
  Definition reqperm_instrs r z :=
    encodeInstrsLW [
        GetWType r_t1 r;
        Sub r_t1 r_t1 (encodeLWordType lwt_cap);
        Mov r_t2 PC;
        Lea r_t2 11;
        Jnz r_t2 r_t1;
        GetP r_t1 r;
         Sub r_t1 r_t1 z
        ; Mov r_t2 PC
        ; Lea r_t2 6
        ; Jnz r_t2 r_t1
        ; Mov r_t2 PC
        ; Lea r_t2 4
        ; Jmp r_t2
        ; Fail
        ; Mov r_t1 0
        ; Mov r_t2 0].

  Lemma reqperm_spec r perm w pc_p pc_b pc_e v a_first w1 w2 φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (reqperm_instrs r (encodePerm perm)))%a →

      ▷ codefrag a_first v (reqperm_instrs r (encodePerm perm))
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ (if isPermLWord w perm then
           ∃ b e a', ⌜w = LCap perm b e a' v⌝ ∧
           (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (reqperm_instrs r (encodePerm perm)))%a v
            ∗ codefrag a_first v (reqperm_instrs r (encodePerm perm)) ∗
            r ↦ᵣ LCap perm b e a' v ∗ r_t1 ↦ᵣ LInt 0%Z ∗ r_t2 ↦ᵣ LInt 0%Z
            -∗ WP Seq (Instr Executable) {{ φ }})
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hφ)".
    codefrag_facts "Hprog".
    iGo "Hprog".
    eapply getwtype_denote ; reflexivity .
    do 3 iInstr "Hprog".
    destruct (is_log_cap w) eqn:Hcap; cycle 1.
    {
      assert (isPermLWord w perm = false) as ->. {destruct_lword w; auto. inversion Hcap. }

      (* if w is not a capability we jump to the failure case *)
      iInstr "Hprog".
     { rewrite -/(encodeLWordType w).
       intros Hcontr; clear -Hcap Hcontr.
        destruct w; [| (destruct sb; [by simpl in Hcap|]) |]
        ; unfold lwt_cap in Hcontr
        ; injection Hcontr
        ; clear Hcontr; intro Hcontr
        ; apply Zminus_eq in Hcontr
        ; match goal with
          | H: encodeLWordType ?x = encodeLWordType ?y |- _ =>
              pose proof (encodeLWordType_correct x y) as Hcontr2 ; cbn in Hcontr2
          end
        ; auto.
      }
      rewrite -/(updatePcPermL (LCap _ _ _ _ _)). rewrite updatePcPermL_cap_non_E;[|inv Hvpc;auto].
      iGo "Hprog".
      by wp_end. }
    {
    (* now we know that w is a capability *)
    assert (∃ p b e a v, w = LCap p b e a v)  as (pc & bc & ec & ac & vc & ->).
    {destruct_lword w ; inversion Hcap. eexists _,_,_,_,_; eauto. }
    rewrite -/(encodeLWordType _).
    simpl_encodeLWordType; rewrite Z.sub_diag.
    do 5 iInstr "Hprog".
    destruct (isPermLWord (LCap pc bc ec ac vc) perm) eqn:Hperm.
    {
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      wp_instr.
      assert (encodePerm pc - encodePerm perm = 0)%Z as ->.
      { inversion Hperm as [Hp]. apply bool_decide_eq_true_1 in Hp as ->. lia. }
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");iFrameAutoSolve.
      iNext. iIntros "(HPC & Hi & Hr_t2 & Hr_t1)". wp_pure.
      iDestruct ("Hcont" with "Hi") as "Hprog".
      iGo "Hprog".
      rewrite -/(updatePcPermL (LCap _ _ _ _ _)).
      rewrite updatePcPermL_cap_non_E;[|inv Hvpc;auto].
      iGo "Hprog".
      iDestruct "Hφ" as (b' e' a' Heq) "Hφ". inv Heq.
      iApply "Hφ"; iFrame. }
    {
      iGo "Hprog".
      inversion Hperm as [Hp]. apply bool_decide_eq_false_1 in Hp. intros Hcontr; inversion Hcontr as [Heq].
      apply Zminus_eq,encodePerm_inj in Heq. subst pc. done.
      rewrite -/(updatePcPermL (LCap _ _ _ _ _)%a).
      rewrite updatePcPermL_cap_non_E;[|inv Hvpc;auto].
      iGo "Hprog".
      iApply wp_value. iFrame. } }
  Qed.

  (* --------------------------------------- REQSIZE ----------------------------------- *)
  (* This macro checks that the capability in r covers a memory range of size
     (i.e. e-b) exactly equal to [minsize]. *)

  Definition reqsize_exact_instrs r (exsize : Z) :=
    encodeInstrsLW
      [ GetB r_t1 r ;
      GetE r_t2 r;
      Sub r_t1 r_t2 r_t1;
      Sub r_t1 r_t1 exsize;
      Mov r_t2 PC;
      Lea r_t2 6;
      Jnz r_t2 r_t1;
      Mov r_t2 PC;
      Lea r_t2 4;
      Jmp r_t2;
      Fail].

  Lemma reqsize_spec r minsize pc_p pc_b pc_e v a_first r_p r_b r_e r_a w1 w2 φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (reqsize_exact_instrs r minsize))%a →

      ▷ codefrag a_first v (reqsize_exact_instrs r minsize)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v
    ∗ ▷ r ↦ᵣ LCap r_p r_b r_e r_a v
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ (if (minsize =? (r_e - r_b)%a)%Z then
           (∃ w1 w2,
            codefrag a_first v (reqsize_exact_instrs r minsize)
            ∗ PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (reqsize_exact_instrs r minsize))%a v
            ∗ r ↦ᵣ LCap r_p r_b r_e r_a v
            ∗ r_t1 ↦ᵣ w1
            ∗ r_t2 ↦ᵣ w2)
           -∗ WP Seq (Instr Executable) {{ φ }}
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hφ)".
    codefrag_facts "Hprog".
    do 6 iInstr "Hprog".

    destruct (minsize =? r_e - r_b)%Z eqn:Hsize.
    { iInstr_lookup "Hprog" as "Hi" "Hcont".
      wp_instr.
      assert (r_e - r_b - minsize = 0)%Z as ->.
      { solve_addr. }
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");iFrameAutoSolve.
      iNext. iIntros "(HPC & Hi & Hr_t2 & Hr_t1)". wp_pure.
      iDestruct ("Hcont" with "Hi") as "Hprog".
      iGo "Hprog".
      rewrite -/(updatePcPermL (LCap pc_p pc_b pc_e (a_first ^+ 11)%a v)).
      rewrite updatePcPermL_cap_non_E;[|by inv Hvpc].
      iApply "Hφ". iExists _,_. iFrame. }
    { iGo "Hprog". intros Hcontr. inv Hcontr. solve_addr.
      rewrite -/(updatePcPermL ((LWSealable (LSCap pc_p pc_b pc_e (a_first ^+ 10)%a v)))).
      rewrite updatePcPermL_cap_non_E;[|by inv Hvpc].
      iGo "Hprog". iApply wp_value. iFrame. }
  Qed.

  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* the following macro clears registers in r. a denotes the list of addresses
     containing the instructions for the clear: |a| = |r| *)
  Definition rclear_instrs (r : list RegName) :=
    encodeInstrsLW (map (λ r_i, Mov r_i 0) r).

  Lemma rclear_instrs_cons rr r: rclear_instrs (rr :: r) = encodeInstrWL (Mov rr 0) :: rclear_instrs r.
  Proof. reflexivity. Qed.

  Lemma rclear_spec (r: list RegName) (rmap : gmap RegName LWord) pc_p pc_b pc_e v a_first φ :
    PC ∉ r →
    r ≠ [] →
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (rclear_instrs r))%a →
    list_to_set r = dom rmap →

      ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v
    ∗ ▷ codefrag a_first v (rclear_instrs r)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (rclear_instrs r))%a v
            ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ LInt 0%Z)
            ∗ codefrag a_first v (rclear_instrs r)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hne Hnnil Hepc Hbounds Hrdom) "(>Hreg & >HPC & >Hrclear & Hφ)".
    iRevert (Hbounds Hrdom).
    iInduction (r) as [| r0 r'] "IH" forall (rmap a_first).
    { congruence. }

    iIntros (? Hrdom). cbn [list_to_set] in Hrdom.
    assert (is_Some (rmap !! r0)) as [r0v Hr0].
    { apply elem_of_dom. rewrite -Hrdom. set_solver. }
    iDestruct (big_sepM_delete _ _ r0 with "Hreg") as "[Hr0 Hreg]". by eauto.
    codefrag_facts "Hrclear".
    iInstr "Hrclear". transitivity (Some (a_first ^+ 1)%a); auto. solve_addr.
    destruct (decide (r' = [])).
    { subst r'. iApply "Hφ". iFrame. iApply (big_sepM_delete _ _ r0); eauto. iFrame.
      rewrite (_: delete r0 rmap = ∅) //. apply dom_empty_inv_L.
      rewrite dom_delete_L -Hrdom. set_solver. }

    iAssert (codefrag (a_first ^+ 1)%a v (rclear_instrs r') ∗
             (codefrag (a_first ^+ 1)%a v (rclear_instrs r') -∗ codefrag a_first v (rclear_instrs (r0 :: r'))))%I
    with "[Hrclear]" as "[Hrclear Hcont]".
    { cbn. unfold codefrag. rewrite (region_mapsto_cons _ (a_first ^+ 1)%a). 2,3: solve_addr.
      iDestruct "Hrclear" as "[? Hr]".
      rewrite (_: ((a_first ^+ 1) ^+ (length (rclear_instrs r')))%a =
                    (a_first ^+ (S (length (rclear_instrs r'))))%a). 2: solve_addr.
      iFrame. eauto. }

    match goal with H : SubBounds _ _ _ _ |- _ =>
      rewrite (_: (a_first ^+ (length (rclear_instrs (r0 :: r'))))%a =
                  ((a_first ^+ 1)%a ^+ length (rclear_instrs r'))%a) in H |- *
    end.
    2: unfold rclear_instrs; cbn; solve_addr.

    destruct (decide (r0 ∈ r')).
    { iDestruct (big_sepM_insert _ _ r0 with "[Hr0 $Hreg]") as "Hreg".
      by rewrite lookup_delete//. by iFrame.
      iApply ("IH" with "[] [] Hreg HPC Hrclear [Hφ Hcont]"); eauto.
      { iPureIntro. set_solver. }
      { iNext. iIntros "(? & Hreg & Hcode)". iApply "Hφ".
        iFrame. iDestruct ("Hcont" with "Hcode") as "Hcode". iFrame.
        iDestruct (big_sepM_insert with "Hreg") as "[? ?]". by rewrite lookup_delete//.
        iApply (big_sepM_delete _ _ r0). done. iFrame. }
      { iPureIntro. solve_pure_addr. }
      { rewrite insert_delete_insert. iPureIntro. set_solver. } }
    { iApply ("IH" with "[] [] Hreg HPC Hrclear [Hφ Hcont Hr0]"); eauto.
      { iPureIntro. set_solver. }
      { iNext. iIntros "(? & Hreg & Hcode)". iApply "Hφ".
        iFrame. iDestruct ("Hcont" with "Hcode") as "Hcode". iFrame.
        iApply (big_sepM_delete _ _ r0). done. iFrame. }
      { iPureIntro. solve_pure_addr. }
      {  iPureIntro. set_solver. } }
  Qed.

End macros.
