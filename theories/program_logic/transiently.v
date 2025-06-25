From iris.proofmode Require Import proofmode classes.
From iris.program_logic Require Export weakestpre.

Section transiently_modality.
  Context `{irisg: irisGS_gen hlc Λ Σ}.

  Definition transiently (Pcommitted : iProp Σ) (Ptransient : iProp Σ) : iProp Σ :=
    Pcommitted ∧ |==> Ptransient.

  Lemma transiently_intro P : P ⊢ transiently P P.
  Proof. now iIntros "$". Qed.

  Lemma transiently_abort Pcommitted Ptransient :
    transiently Pcommitted Ptransient ⊢ Pcommitted.
  Proof. now iIntros "[P _]". Qed.

  Lemma transiently_commit Pcommitted Ptransient :
    transiently Pcommitted Ptransient ⊢ |==> Ptransient.
  Proof. now iIntros "[_ Ht]". Qed.

  Lemma transiently_mono_2 Pcommitted Ptransient1 (Ptransient2 : iProp Σ) :
    (Ptransient1 ==∗ Ptransient2) ∗
      transiently Pcommitted Ptransient1 ⊢ transiently Pcommitted Ptransient2.
  Proof. iIntros "(HPt & Hcomtrans1)". iSplit.
         - now iDestruct "Hcomtrans1" as "($ & _)".
         - iDestruct "Hcomtrans1" as "(_ & Htrans1)".
           iMod "Htrans1" as "Htrans1".
           now iMod ("HPt" with "Htrans1").
  Qed.

  Lemma transiently_proper_strong {P Q R : iProp Σ} :
    (Q -∗ R) ∗ transiently P Q ⊢ transiently P R.
  Proof.
    iIntros "(HQR & HPQ)".
    iSplit; first by iDestruct "HPQ" as "(HP & _)".
    iDestruct "HPQ" as "(_ & HQ)".
    iMod "HQ" as "HQ".
    now iApply "HQR".
  Qed.

  #[export] Instance elimModal_transiently {P Q R} : ElimModal True false false (transiently P Q) Q (transiently P R) (|==> R).
  Proof.
    iIntros (_) "(HPQ & HK)".
    now iApply (transiently_mono_2 with "[$HK $HPQ]").
  Qed.
End transiently_modality.
