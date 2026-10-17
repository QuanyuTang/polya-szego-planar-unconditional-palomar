module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PlanarBucklingSolution

/-!
# Complete solution target types and axiom guards

SOURCE_DRAFT: these five guards have not run. This audit imports only the
standalone solution, not Challenge with its intentionally omitted proofs.
The original theorem definitions and the exact open-disk conclusion remain
those of the complete literal standalone solution. An expected message in
this file is a requested check, not verification evidence.
-/

@[expose] public section
set_option pp.universes true

#check @BucklingChallenge.area_inequality
/-- info: 'BucklingChallenge.area_inequality' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms BucklingChallenge.area_inequality

#check @BucklingChallenge.area_equality_iff
/-- info: 'BucklingChallenge.area_equality_iff' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms BucklingChallenge.area_equality_iff

#check @BucklingChallenge.polya_szego_buckling
/-- info: 'BucklingChallenge.polya_szego_buckling' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms BucklingChallenge.polya_szego_buckling

#check @BucklingChallenge.bucklingEig_ball
/-- info: 'BucklingChallenge.bucklingEig_ball' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms BucklingChallenge.bucklingEig_ball

#check @BucklingChallenge.buckling_ge_dirichlet
/-- info: 'BucklingChallenge.buckling_ge_dirichlet' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms BucklingChallenge.buckling_ge_dirichlet

end
