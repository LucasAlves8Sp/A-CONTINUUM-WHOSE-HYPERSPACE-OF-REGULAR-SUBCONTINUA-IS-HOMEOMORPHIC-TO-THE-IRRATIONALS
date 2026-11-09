import RegSub

/-! Run `lake env lean CheckAxioms.lean` to list the axioms used by the main results. -/

-- Theorem A, unconditional
#print axioms RegSub.theoremA_l2
#print axioms RegSub.theoremA_unconditional
#print axioms RegSub.DX_homeomorph_baire

-- the two former hypotheses, now proved
#print axioms RegSub.alexandrovUrysohnStatement
#print axioms RegSub.geometricIdentification

-- known results proved along the way
#print axioms RegSub.alexandrovUrysohn
#print axioms RegSub.baire_homeomorph_irr
#print axioms RegSub.isGδ_polishSpace
#print axioms RegSub.eq_univ_of_interior_nonempty
#print axioms RegSub.isConnected_knaster
#print axioms RegSub.exists_template

-- the geometric results of the paper
#print axioms RegSub.Y_eq
#print axioms RegSub.Y_inter_Z
#print axioms RegSub.isCompact_X
#print axioms RegSub.isConnected_X
#print axioms RegSub.nontrivial_X
#print axioms RegSub.piece_subset_closure_relInt_block
#print axioms RegSub.X_subset_closure_Ublk
#print axioms RegSub.piece_subset_of_crossing
#print axioms RegSub.piece_subset_of_relInt
#print axioms RegSub.eq_closure_blocks
#print axioms RegSub.pcs_admissible
#print axioms RegSub.reg_Psi
#print axioms RegSub.pcs_Psi
#print axioms RegSub.hausdorffDist_Psi_le
#print axioms RegSub.PhiHomeo

-- the code space
#print axioms RegSub.pathConvex_iff_parentClosed
#print axioms RegSub.codeSet_nonempty
#print axioms RegSub.isGδ_codeSet
#print axioms RegSub.instZeroDimensionalSpaceCodeSet
#print axioms RegSub.isCompact_interior_eq_empty
#print axioms RegSub.codeSet_homeomorph_baire
#print axioms RegSub.theoremA
