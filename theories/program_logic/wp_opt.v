From iris.proofmode Require Import proofmode classes.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export transiently.


Section wp_opt.
  Context `{irisg: irisGS_gen hlc Λ Σ}.

  Implicit Types P Q : iProp Σ.

  Definition wp_opt {A} (φ : option A) (Φf : iProp Σ) (Φs : A -> iProp Σ) : iProp Σ :=
    match φ with
      None => Φf
    | Some φ' => Φs φ'
    end.

  Lemma wp_opt_unfold {A} {φ : option A} {Φf Φs} :
    (⌜ φ = None ⌝ -∗ Φf) ∧ (∀ x, ⌜ φ = Some x ⌝ -∗ Φs x)
    ⊢ wp_opt φ Φf Φs.
  Proof.
    iIntros "H".
    destruct φ; [rewrite bi.and_elim_r| rewrite bi.and_elim_l];
      now iApply "H".
  Qed.

  Lemma wp_opt_eqn {A} (φ : option A) (Φf : iProp Σ) (Φs : A -> iProp Σ) :
    wp_opt φ Φf (fun x => ⌜ φ = Some x ⌝ → Φs x) ⊢ wp_opt φ Φf Φs.
  Proof.
    destruct φ; cbn; last done.
    iIntros "Hk".
    now iApply "Hk".
  Qed.

  Lemma wp_opt_is_Some {A Φs Φf} {φ : option A} : is_Some (φ) -> wp_opt φ Φf Φs ⊢ wp_opt φ False Φs.
  Proof.
    destruct φ; first by cbn.
    now inversion 1.
  Qed.

  Lemma wp_opt_univ {A Φs} {φ : option A} : (∀ x, Φs x) ⊢ wp_opt φ True Φs.
  Proof.
    iIntros "H".
    now destruct φ.
  Qed.

  Lemma wp_opt_bind {A B} {φ : option A} {K : A -> option B} {Φf Φs} :
    wp_opt φ Φf (fun φ' => wp_opt (K φ') Φf Φs) ⊣⊢
      wp_opt (φ ≫= K) Φf Φs.
  Proof.
    destruct φ; now cbn.
  Qed.

  Lemma wp_opt_mono {A} {m : option A} {Φf Φs1 Φs2} :
    (∀ x, Φs1 x -∗ Φs2 x) ∗ wp_opt m Φf Φs1 ⊢ wp_opt m Φf Φs2.
  Proof.
    iIntros "(HΦs & Hwp)".
    destruct m; cbn; last done.
    now iApply "HΦs".
  Qed.

  Definition wp_opt2 {A1 A2} (φ1 : option A1) (φ2 : option A2) (Φf : iProp Σ) (Φs : A1 -> A2 -> iProp Σ) : iProp Σ :=
    match φ1 , φ2 with
      None , None => |==> Φf
    | Some x1 , Some x2 => |==> Φs x1 x2
    | _ , _ => False
    end.

  Lemma wp2_diag_univ {A} {φ : option A} {Φf} {Φs : A -> A -> iProp Σ} :
    (Φf ∧ (∀ x, Φs x x)) ⊢ wp_opt2 φ φ Φf Φs.
  Proof.
    destruct φ; [rewrite bi.and_elim_r | rewrite bi.and_elim_l];
      now iIntros "Hk".
  Qed.

  Lemma wp_wp2 {Ep} {A1 A2} {φ1 : option A1} {φ2 : option A2} {Φf Φs} :
    wp_opt2 φ1 φ2 Φf (fun x1 x2 => Φs x2) ⊢ wp_opt φ2 (|={Ep}=> Φf) (fun x => |={Ep}=> Φs x).
  Proof.
    iIntros "Hk".
    destruct φ1 , φ2.
    - now iMod "Hk" as "Hk".
    - now cbn.
    - now cbn.
    - now iMod "Hk" as "Hk".
  Qed.

  Lemma wp2_val {A1 A2} {x1 : A1} {x2 : A2} {Φf Φs} :
    (|==> Φs x1 x2) ⊢ wp_opt2 (Some x1) (Some x2) Φf Φs.
  Proof.
    now iIntros "Hk".
  Qed.

  Lemma wp_opt2_eqn {A1 A2} {φ1 : option A1} {φ2 : option A2} (Φf : iProp Σ) (Φs : A1 -> A2 -> iProp Σ) :
    wp_opt2 φ1 φ2 Φf (fun x1 x2 => ⌜ φ1 = Some x1 ⌝ → ⌜ φ2 = Some x2 ⌝ → Φs x1 x2) ⊢ wp_opt2 φ1 φ2 Φf Φs.
  Proof.
    destruct φ1, φ2; cbn; try done.
    iIntros "Hk".
    now iApply "Hk".
  Qed.

  Lemma wp_opt2_eqn_both {A1 A2} {φ1 : option A1} {φ2 : option A2} (Φf : iProp Σ) (Φs : A1 -> A2 -> iProp Σ) :
    wp_opt2 φ1 φ2 (⌜ φ1 = None ⌝ → ⌜ φ2 = None ⌝ → Φf) (fun x1 x2 => ⌜ φ1 = Some x1 ⌝ → ⌜ φ2 = Some x2 ⌝ → Φs x1 x2) ⊢ wp_opt2 φ1 φ2 Φf Φs.
  Proof.
    destruct φ1, φ2; cbn; try done.
    - iIntros "Hk".
      now iApply "Hk".
    - iIntros "Hk".
      now iApply "Hk".
  Qed.

  Lemma wp_opt2_mod {A1 A2} {φ1 : option A1} {φ2 : option A2} {Φf Φs} :
    (|==> wp_opt2 φ1 φ2 Φf Φs) ⊢ wp_opt2 φ1 φ2 Φf Φs.
  Proof.
    destruct φ1, φ2; now iIntros ">H".
  Qed.

  Lemma wp_opt2_bind {A1 A2} {B1 B2} {φ1 : option A1} {φ2 : option A2} {k1 : A1 -> option B1} {k2 : A2 -> option B2} {Φf Φs} :
    wp_opt2 φ1 φ2 Φf (fun x1 x2 => wp_opt2 (k1 x1) (k2 x2) Φf Φs) ⊢
      wp_opt2 (x1 ← φ1 ; k1 x1) (x2 ← φ2 ; k2 x2) Φf Φs.
  Proof.
    iIntros "Hk".
    iApply wp_opt2_mod.
    destruct φ1, φ2.
    - now iMod "Hk" as "Hk".
    - now cbn.
    - now cbn.
    - now iMod "Hk" as "Hk".
  Qed.

  Lemma wp_opt2_mono {A1 A2} {φ1 : option A1} {φ2 : option A2} {Φf Φsa Φsb} :
    (∀ x1 x2, Φsa x1 x2 -∗ Φsb x1 x2) ∗ wp_opt2 φ1 φ2 Φf Φsa ⊢ wp_opt2 φ1 φ2 Φf Φsb.
  Proof.
    destruct φ1, φ2; cbn; iIntros "(Hab & Hwp)"; try done.
    now iApply "Hab".
  Qed.

  Lemma wp_opt2_frame {A1 A2} {φ1 : option A1} {φ2 : option A2} {Φf Φs R} :
    ⊢ R -∗ wp_opt2 φ1 φ2 Φf Φs -∗ wp_opt2 φ1 φ2 (R ∗ Φf) (fun x1 x2 => R ∗ Φs x1 x2).
  Proof.
    iIntros "HR Hwp".
    destruct φ1, φ2; now iFrame.
  Qed.

  Lemma wp_opt2_mono2 {A1 A2} {φ1 : option A1} {φ2 : option A2} {Φfa Φfb Φsa Φsb} :
    (( Φfa -∗ Φfb) ∧ (∀ x1 x2, Φsa x1 x2 -∗ Φsb x1 x2)) ∗ wp_opt2 φ1 φ2 Φfa Φsa ⊢ wp_opt2 φ1 φ2 Φfb Φsb.
  Proof.
    destruct φ1, φ2; cbn; iIntros "[Hfsab Hwp]"; try done.
    - iDestruct "Hfsab" as "(_ & Hsab)".
      now iApply "Hsab".
    - iDestruct "Hfsab" as "(Hfab & _)".
      now iApply "Hfab".
  Qed.

  Lemma transiently_wp_opt2 {A1 A2 : Type} {P : iProp Σ} {φ1 : option A1} {φ2 : option A2} {Φf Φsa} :
    transiently P (wp_opt2 φ1 φ2 Φf Φsa) ⊢
      wp_opt2 φ1 φ2 (transiently P Φf) (fun x1 x2 => transiently P (Φsa x1 x2)).
  Proof.
    iIntros "HPQ".
    destruct φ1 eqn:Hφ1; destruct φ2 eqn:Hφ2; cbn.
    - iApply (transiently_mono_2 with "[$HPQ]").
      now iIntros ">HΦsa".
    - now iMod (transiently_commit with "HPQ") as "%f".
    - now iMod (transiently_commit with "HPQ") as "%f".
    - iApply (transiently_mono_2 with "[$HPQ]").
      now iIntros ">HΦsa".
  Qed.

End wp_opt.
