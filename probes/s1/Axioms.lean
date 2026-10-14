/- S1 review probe: kernel axioms of the Stage-1 theorems and controls, and the signatures
of the trusted definitions (which instance arguments they really take). -/
import RecursionFast.Contract
import RecursionFast.Library
import RecursionFast.Controls

open RecursionFast RecursionFast.Controls RecursionFast.Codec

#check @Layout.rel
#check @Gadget.holds
#check @Table.msgs
#check @Layout.Admissible
#check @relK

#print axioms toy_secure
#print axioms toy20_secure
#print axioms toyDecide_iff
#print axioms toy_accepts_iff
#print axioms R1CS_iff_layout
#print axioms rel_r1csWit_iff
#print axioms R1CS_of_rel
#print axioms rel_r1csLayout_iff
#print axioms Gadget.holds_iff
#print axioms rowDot_eq
#print axioms rel_trim_iff
#print axioms rel_normal_iff
#print axioms relBelow_iff
#print axioms pLayout_eLayout
#print axioms pWit_eWit
#print axioms eLayout_length
#print axioms eWit_length
#print axioms R1CS_iff_rel
#print axioms r1csLayout_admissible
#print axioms r1cs_pos
#print axioms r1cs_neg
#print axioms r1cs_iff
#print axioms r1cs_one_pos
#print axioms r1cs_one_neg
#print axioms r1cs_relK
#print axioms eqMult_neg
#print axioms fixedHeight_neg
#print axioms wrap_pos
#print axioms wrap_neg
#print axioms fib_garbage
#print axioms fib_boundary_neg
#print axioms twoChip_pos
#print axioms twoChip_neg
#print axioms twoChip_admissible
#print axioms lookup_pos
#print axioms lookup_neg
#print axioms lookup_neg_fixed
#print axioms lookup_admissible
#print axioms fib_pos
#print axioms fib_neg
#print axioms fib_admissible
#print axioms stmt_neg
#print axioms noPub_neg
#print axioms twoChip_noPub
#print axioms emptyPub_neg
#print axioms unsat_neg
#print axioms unsat_admissible
#print axioms unsat_admissible_of
#print axioms cells_neg
#print axioms cols_neg
#print axioms pubCols_neg
#print axioms entries_neg
#print axioms fixedCells_neg
#print axioms chips_cap
#print axioms ports_cap
#print axioms msg_cap
#print axioms bus_cap
#print axioms sel_own
#print axioms cols_pos
#print axioms t_cap
#print axioms cons_cap
#print axioms q_cap
#print axioms degree_cap
#print axioms hit_secure
#print axioms triv_relK
#print axioms acceptAll_no_KSF
#print axioms rejectAll_not_complete
#print axioms rejectAll_not_secure
#print axioms acceptAllChal_rbr_one
#print axioms acceptAllChal_complete
#print axioms acceptAllChal_err_ge_one
#print axioms acceptAllChal_not_secure
