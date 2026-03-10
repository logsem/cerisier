From cap_machine Require
  fundamental
  soc_adequacy
  mutual_attestation_adequacy
  trusted_memory_readout_adequacy
.

Goal True. idtac "
Assumptions of fundamental theorem:". Abort.
Print Assumptions fundamental.fundamental'.

Goal True. idtac "
Assumptions of SOC end-to-end theorem:". Abort.
Print Assumptions soc_adequacy.soc_enclaves_adequacy.

Goal True. idtac "
Assumptions of trusted memory readout end-to-end theorem:". Abort.
Print Assumptions trusted_memory_readout_adequacy.ts_enclaves_adequacy.

Goal True. idtac "
Assumptions of mutual attestation end-to-end theorem:". Abort.
Print Assumptions mutual_attestation_adequacy.ma_enclaves_adequacy.
