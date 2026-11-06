import DFSLean
import DFSLean.Spec
import DFSLean.Spec2

/-! Every proved theorem has exactly the type of the frozen specification `DFS.Spec.*`. -/

example : type_of% @DFS.Spec.F_bound := @DFS.F_bound
example : type_of% @DFS.Spec.IsSol.lipschitz := @DFS.IsSol.lipschitz
example : type_of% @DFS.Spec.IsSol.slope_lin₂ := @DFS.IsSol.slope_lin₂
example : type_of% @DFS.Spec.IsSol.barrier := @DFS.IsSol.barrier
example : type_of% @DFS.Spec.IsSol.reach := @DFS.IsSol.reach
example : type_of% @DFS.Spec.IsSol.rescale := @DFS.IsSol.rescale
example : type_of% @DFS.Spec.IsSol.mono_x2 := @DFS.IsSol.mono_x2
example : type_of% @DFS.Spec.IsSol.mono_y2 := @DFS.IsSol.mono_y2
example : type_of% @DFS.Spec.IsSol.good := @DFS.IsSol.good
example : type_of% @DFS.Spec.log_growth := @DFS.log_growth
example : type_of% @DFS.Spec.log_growth_asymp := @DFS.log_growth_asymp
example : type_of% @DFS.Spec.item1 := @DFS.item1
example : type_of% @DFS.Spec.item2 := @DFS.item2
example : type_of% @DFS.Spec.lyapunov_state := @DFS.lyapunov_state
example : type_of% @DFS.Spec.item3 := @DFS.item3
example : type_of% @DFS.Spec.growth_coeffs := @DFS.growth_coeffs
example : type_of% @DFS.Spec.item4 := @DFS.item4
example : type_of% @DFS.Spec.four_parameter_log_convergence := @DFS.four_parameter_log_convergence

#print axioms DFS.four_parameter_log_convergence
#print axioms DFS.log_growth

/-! Stages 2–4. -/

example : type_of% @DFS.Spec.IsSol_iff_IsDI := @DFS.IsSol_iff_IsDI
example : type_of% @DFS.Spec.IsDI.mono := @DFS.IsDI.mono
example : type_of% @DFS.Spec.IsDI.shift := @DFS.IsDI.shift
example : type_of% @DFS.Spec.IsDI.slope_dot := @DFS.IsDI.slope_dot
example : type_of% @DFS.Spec.IsDI.dot_le := @DFS.IsDI.dot_le
example : type_of% @DFS.Spec.IsDI.barrier := @DFS.IsDI.barrier
example : type_of% @DFS.Spec.IsDI.reach := @DFS.IsDI.reach
example : type_of% @DFS.Spec.exists_IsDI := @DFS.exists_IsDI
example : type_of% @DFS.Spec.V8_nonempty := @DFS.V8_nonempty
example : type_of% @DFS.Spec.V8_convex := @DFS.V8_convex
example : type_of% @DFS.Spec.V8_closed := @DFS.V8_closed
example : type_of% @DFS.Spec.V8_bounded := @DFS.V8_bounded
example : type_of% @DFS.Spec.V8_usc := @DFS.V8_usc
example : type_of% @DFS.Spec.exists_IsSol8 := @DFS.exists_IsSol8
example : type_of% @DFS.Spec.head1_eq_pair := @DFS.head1_eq_pair
example : type_of% @DFS.Spec.head2_eq_pair := @DFS.head2_eq_pair
example : type_of% @DFS.Spec.coef1_perm := @DFS.coef1_perm
example : type_of% @DFS.Spec.coef2_perm := @DFS.coef2_perm
example : type_of% @DFS.Spec.logit_perm := @DFS.logit_perm
example : type_of% @DFS.Spec.prob_perm := @DFS.prob_perm
example : type_of% @DFS.Spec.lossInst_perm := @DFS.lossInst_perm
example : type_of% @DFS.Spec.lossTrain_perm := @DFS.lossTrain_perm
example : type_of% @DFS.Spec.fixed_iff := @DFS.fixed_iff
example : type_of% @DFS.Spec.lossTrain_iota := @DFS.lossTrain_iota
example : type_of% @DFS.Spec.gInst_perm := @DFS.gInst_perm
example : type_of% @DFS.Spec.VelM_perm := @DFS.VelM_perm
example : type_of% @DFS.Spec.Sel_iota := @DFS.Sel_iota
example : type_of% @DFS.Spec.gTrain_iota := @DFS.gTrain_iota
example : type_of% @DFS.Spec.IsSol8.iota := @DFS.IsSol8.iota
example : type_of% @DFS.Spec.lossInst_hasFDerivAt := @DFS.lossInst_hasFDerivAt
example : type_of% @DFS.Spec.lossTrain_hasFDerivAt := @DFS.lossTrain_hasFDerivAt
example : type_of% @DFS.Spec.loss8_hasFDerivAt := @DFS.loss8_hasFDerivAt
example : type_of% @DFS.Spec.logit_of_ne := @DFS.logit_of_ne
example : type_of% @DFS.Spec.head1_iota := @DFS.head1_iota
example : type_of% @DFS.Spec.head2_iota := @DFS.head2_iota
example : type_of% @DFS.Spec.g8_on_R := @DFS.g8_on_R
example : type_of% @DFS.Spec.g8_bound_on_R := @DFS.g8_bound_on_R
example : type_of% @DFS.Spec.lemmaC2_region := @DFS.lemmaC2_region
example : type_of% @DFS.Spec.lemmaC2_mono := @DFS.lemmaC2_mono
example : type_of% @DFS.Spec.lemmaC2_lip := @DFS.lemmaC2_lip
example : type_of% @DFS.Spec.lemmaC2_initial := @DFS.lemmaC2_initial
example : type_of% @DFS.Spec.corC3 := @DFS.corC3
example : type_of% @DFS.Spec.trace_length_le := @DFS.trace_length_le
example : type_of% @DFS.Spec.genLoss_bound := @DFS.genLoss_bound
example : type_of% @DFS.Spec.learning_dynamics := @DFS.learning_dynamics

#print axioms DFS.learning_dynamics
#print axioms DFS.IsSol8.iota
#print axioms DFS.exists_IsSol8
#print axioms DFS.lossTrain_hasFDerivAt
#print axioms DFS.VelM_perm
