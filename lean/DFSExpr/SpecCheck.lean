import DFSExpr
import DFSExpr.Spec

/-! Every proved theorem has exactly the type of the frozen specification `DFSExpr.Spec.*`,
and depends only on Lean's standard axioms. -/

example : type_of% @DFSExpr.Spec.one_layer_lower_bound := @DFSExpr.one_layer_lower_bound
example : type_of% @DFSExpr.Spec.dense_lower_bound := @DFSExpr.dense_lower_bound
example : type_of% @DFSExpr.Spec.dfs_lower_bound := @DFSExpr.dfs_lower_bound
example : type_of% @DFSExpr.Spec.softmax_gap := @DFSExpr.softmax_gap
example : type_of% @DFSExpr.Spec.pos_selector := @DFSExpr.pos_selector
example : type_of% @DFSExpr.Spec.first_layer := @DFSExpr.first_layer
example : type_of% @DFSExpr.Spec.dfs_transitions := @DFSExpr.dfs_transitions
example : type_of% @DFSExpr.Spec.dfs_length := @DFSExpr.dfs_length
example : type_of% @DFSExpr.Spec.two_layer_core := @DFSExpr.two_layer_core
example : type_of% @DFSExpr.Spec.two_layer_dfs := @DFSExpr.two_layer_dfs
example : type_of% @DFSExpr.Spec.dm_efficiency := @DFSExpr.dm_efficiency
example : type_of% @DFSExpr.Spec.k_layer_efficiency := @DFSExpr.k_layer_efficiency
example : type_of% @DFSExpr.Spec.mem_support := @DFSExpr.mem_support
example : type_of% @DFSExpr.Spec.lookahead_transformer := @DFSExpr.lookahead_transformer

#print axioms DFSExpr.one_layer_lower_bound
#print axioms DFSExpr.dense_lower_bound
#print axioms DFSExpr.dfs_lower_bound
#print axioms DFSExpr.first_layer
#print axioms DFSExpr.two_layer_dfs
#print axioms DFSExpr.dm_efficiency
#print axioms DFSExpr.k_layer_efficiency
#print axioms DFSExpr.lookahead_transformer
