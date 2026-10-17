module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import UnconditionalAreaRigidity

/-!
# Complete public types and exact axiom guards for the final source assembly

SOURCE_DRAFT (2026-10-17): NOT COMPILED OR REGISTERED.
These are requested checks, not successful-check evidence. In particular,
an expected guard message in this source is not a statement that the guard
has run. The complete final dependency chain still needs native checking.
-/

@[expose] public section

set_option pp.universes true

#check @Buckling.DirichletFKAreaProduct.sharpConstant_pos
/-- info: 'Buckling.DirichletFKAreaProduct.sharpConstant_pos' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.DirichletFKAreaProduct.sharpConstant_pos

#check @Buckling.DirichletFKAreaProduct.global_lower_bound
/-- info: 'Buckling.DirichletFKAreaProduct.global_lower_bound' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.DirichletFKAreaProduct.global_lower_bound

#check @Buckling.FaberKrahnEqualityGroundStateData.exists_density_with_global_branches
/-- info: 'Buckling.FaberKrahnEqualityGroundStateData.exists_density_with_global_branches' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.FaberKrahnEqualityGroundStateData.exists_density_with_global_branches

#check @Buckling.FaberKrahnEqualityAeDisk.exists_ae_disk_of_area_product_equality
/-- info: 'Buckling.FaberKrahnEqualityAeDisk.exists_ae_disk_of_area_product_equality' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.FaberKrahnEqualityAeDisk.exists_ae_disk_of_area_product_equality

#check @Buckling.FaberKrahnEqualityAeDisk.exists_prescribed_ae_disk_of_area_product_equality
/-- info: 'Buckling.FaberKrahnEqualityAeDisk.exists_prescribed_ae_disk_of_area_product_equality' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.FaberKrahnEqualityAeDisk.exists_prescribed_ae_disk_of_area_product_equality

#check @Buckling.AffineReflectionWeakTransport.whole_data_reflection
/-- info: 'Buckling.AffineReflectionWeakTransport.whole_data_reflection' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.AffineReflectionWeakTransport.whole_data_reflection

#check @Buckling.WeakSMPConnected.zero_or_pos_ae
/-- info: 'Buckling.WeakSMPConnected.zero_or_pos_ae' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.WeakSMPConnected.zero_or_pos_ae

#check @Buckling.FaberKrahnPolarizationBranch.global_branch_of_groundState_at_equality
/-- info: 'Buckling.FaberKrahnPolarizationBranch.global_branch_of_groundState_at_equality' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.FaberKrahnPolarizationBranch.global_branch_of_groundState_at_equality

#check @Buckling.ReflectionBranchPositiveBall.exists_pos_ball_ae_eq_of_nonneg_branches
/-- info: 'Buckling.ReflectionBranchPositiveBall.exists_pos_ball_ae_eq_of_nonneg_branches' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.ReflectionBranchPositiveBall.exists_pos_ball_ae_eq_of_nonneg_branches

#check @Buckling.faberKrahn_holds_without_E12
/-- info: 'Buckling.faberKrahn_holds_without_E12' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.faberKrahn_holds_without_E12

#check @Buckling.paperExternals_holds_without_E12
/-- info: 'Buckling.paperExternals_holds_without_E12' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.paperExternals_holds_without_E12

#check @Buckling.area_inequality_unconditional
/-- info: 'Buckling.area_inequality_unconditional' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.area_inequality_unconditional

#check @Buckling.area_equality_iff_without_E12
/-- info: 'Buckling.area_equality_iff_without_E12' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.area_equality_iff_without_E12

#check @Buckling.polya_szego_buckling_without_E12
/-- info: 'Buckling.polya_szego_buckling_without_E12' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms Buckling.polya_szego_buckling_without_E12

end
