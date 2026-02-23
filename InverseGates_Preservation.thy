theory InverseGates_Preservation
  imports Main
begin

datatype gate = H | X | Y | Z | S | Sdg | T | Tdg

fun inverse_of :: "gate => gate" where
  "inverse_of H = H"
| "inverse_of X = X"
| "inverse_of Y = Y"
| "inverse_of Z = Z"
| "inverse_of S = Sdg"
| "inverse_of Sdg = S"
| "inverse_of T = Tdg"
| "inverse_of Tdg = T"

fun inverse_pair_seq :: "gate => gate list" where
  "inverse_pair_seq g = [g, inverse_of g]"

definition composite_aux_seq :: "gate list" where
  "composite_aux_seq = [H, H, Z, X, Z, X]"

definition composite_res_seq :: "gate list" where
  "composite_res_seq = [X, Z, X, Z, H, H]"

definition composite_seq :: "gate list" where
  "composite_seq = composite_aux_seq @ composite_res_seq"

locale gate_semantics =
  fixes U :: "gate => 's => 's"
  assumes inverse_axiom: "U (inverse_of g) o U g = id"
begin

fun eval_seq :: "gate list => 's => 's" where
  "eval_seq [] = id"
| "eval_seq (g # gs) = eval_seq gs o U g"

lemma eval_seq_append:
  "eval_seq (xs @ ys) = eval_seq ys o eval_seq xs"
  by (induction xs) auto

lemma eval_inverse_pair_identity:
  "eval_seq (inverse_pair_seq g) = id"
  using inverse_axiom by simp

lemma eval_composite_identity:
  "eval_seq composite_seq = id"
  unfolding composite_seq_def composite_aux_seq_def composite_res_seq_def
  by simp

definition insert_at :: "nat => gate list => gate list => gate list" where
  "insert_at i ins circ = take i circ @ ins @ drop i circ"

lemma eval_insert_identity:
  assumes "eval_seq ins = id"
  shows "eval_seq (insert_at i ins circ) = eval_seq circ"
proof -
  have "eval_seq (insert_at i ins circ)
      = eval_seq (drop i circ) o eval_seq ins o eval_seq (take i circ)"
    unfolding insert_at_def
    by (simp add: eval_seq_append o_assoc)
  also have "... = eval_seq (drop i circ) o eval_seq (take i circ)"
    using assms by simp
  also have "... = eval_seq circ"
    by (simp add: eval_seq_append[symmetric] append_take_drop_id)
  finally show ?thesis .
qed

theorem inverse_pair_insert_preserves:
  "eval_seq (insert_at i (inverse_pair_seq g) circ) = eval_seq circ"
  using eval_insert_identity eval_inverse_pair_identity by simp

theorem composite_insert_preserves:
  "eval_seq (insert_at i composite_seq circ) = eval_seq circ"
  using eval_insert_identity eval_composite_identity by simp

end

end
