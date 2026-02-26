theory Insertion
  imports Main
begin

(*
  Insertion.thy

  Goal
    Formalize list-level and circuit-level obfuscation primitives and prove that
    they preserve semantics when the inserted or replacing sequence is semantics-preserving.

  What is in this theory
    1) A small datatype of single-qubit gates (H, X, Y, Z, S, Sdg, T, Tdg).
    2) A locale gate_semantics that abstracts gate meaning as a state transformer U.
    3) Sequence execution apply_seq, plus inverse-sequence construction inv_seq.
    4) Insertion on a gate list insert_at and a proof that inserting an identity
       sequence does not change apply_seq.
    5) Replacement on a gate list replace_at and a proof that replacing a target
       gate with an equivalent sequence does not change apply_seq.

  Notes
    - This theory is intentionally abstract: it does not commit to matrices.
    - cloaked and delayed are left abstract but constrained by axioms cloaked_ok, delayed_ok.
*)


(* A finite set of primitive single-qubit gates we care about in the obfuscation recipes. *)
datatype gate = H | X | Y | Z | S | Sdg | T | Tdg

(* gate is a matrix of some dimension n*n 
 s is a vector of that dimension
*)
(*
  gate_semantics
    - U maps a gate to a semantic transformer on an abstract state 's.
    - cloaked and delayed are families of gate sequences used for replacement obfuscation.
    - Assumptions state the algebraic identities needed for cancellation and inverses.
*)
locale gate_semantics =
  fixes U :: "gate \<Rightarrow> 's \<Rightarrow> 's"
    and cloaked :: "gate \<Rightarrow> nat \<Rightarrow> gate list"
    and delayed :: "gate \<Rightarrow> nat \<Rightarrow> gate list"
  assumes H_H:  "U H (U H s) = s"
      and X_X:  "U X (U X s) = s"
      and Y_Y:  "U Y (U Y s) = s"
      and Z_Z:  "U Z (U Z s) = s"
      and S_Sdg:    "U Sdg (U S s) = s"  "U S (U Sdg s) = s"
      and T_Tdg:    "U Tdg (U T s) = s"  "U T (U Tdg s) = s"
      and cloaked_ok:
        "\<forall>g v s. apply_seq (cloaked g v) s = U g s"
      and delayed_ok:
        "\<forall>g v s. apply_seq (delayed g v) s = U g s"
begin

(* Execute a list of gates as repeated application of U. *)
fun apply_seq :: "gate list \<Rightarrow> 's \<Rightarrow> 's" where
  "apply_seq [] s = s"
| "apply_seq (g # gs) s = apply_seq gs (U g s)"


(* Inverse of a primitive gate in our datatype. *)
fun inv_of :: "gate \<Rightarrow> gate" where
  "inv_of H = H"
| "inv_of X = X"
| "inv_of Y = Y"
| "inv_of Z = Z"
| "inv_of S = Sdg"
| "inv_of Sdg = S"
| "inv_of T = Tdg"
| "inv_of Tdg = T"


(* Inverse sequence of xs, computed as reverse xs and map inv_of. *)
definition inv_seq :: "gate list \<Rightarrow> gate list" where
  "inv_seq xs = map inv_of (rev xs)"


(*
  Composite-gate insertion sequences
    aux_seq is inserted before, res_seq after, and they cancel (identity) when adjacent.
    We prove that by showing res_seq = inv_seq aux_seq.
*)
definition aux_seq :: "gate list" where
  "aux_seq = [H, H, Z, X, Z, X]"

definition res_seq :: "gate list" where
  "res_seq = [X, Z, X, Z, H, H]"

definition aux_res_seq :: "gate list" where
  "aux_res_seq = aux_seq @ res_seq"


(*
  invpair g is the generic insertion: [g] followed by its inverse, so it is identity.
  This version uses inv_seq [g] rather than a hand-written case split.
*)
definition invpair :: "gate \<Rightarrow> gate list" where
  "invpair g = [g] @ inv_seq [g]"


(* Insert a gate sequence ins into a gate list xs at position k (0-based). *)
fun insert_at :: "nat \<Rightarrow> gate list \<Rightarrow>gate list \<Rightarrow>gate list" where
  "insert_at 0 ins xs = ins @ xs"
| "insert_at (Suc n) ins [] = ins"          (* or ins @ [] depending on your choice *)
| "insert_at (Suc n) ins (x#xs) = x # insert_at n ins xs"


(* Sequencing lemma: executing xs @ ys is executing xs then ys. *)
lemma apply_seq_append:
  "apply_seq (xs @ ys) s = apply_seq ys (apply_seq xs s)"
  by (induct xs arbitrary: s) auto


(* One-step cancellation: inv_of g composed after g gives identity on the state. *)
lemma inv_of_cancel: "U (inv_of g) (U g s) = s"
  by (cases g; simp add: H_H X_X Y_Y Z_Z S_Sdg T_Tdg)


(* Whole-sequence cancellation: xs followed by inv_seq xs is identity. *)
lemma apply_seq_inv_seq:
  "apply_seq (xs @ inv_seq xs) s = s"
  unfolding inv_seq_def
  by (induct xs arbitrary: s) (auto simp: apply_seq_append inv_of_cancel)

lemma res_is_inverse_aux:
  "res_seq = inv_seq aux_seq"
  unfolding res_seq_def aux_seq_def inv_seq_def
  by simp


(* aux_seq @ res_seq is identity, once we establish res_seq is inv_seq aux_seq. *)
lemma aux_res_id:
  "\<forall>s. apply_seq aux_res_seq s = s"
  by (intro allI) (simp add: aux_res_seq_def res_is_inverse_aux apply_seq_inv_seq)

  (* 
    proof
      fix s
      have "apply_seq aux_res_seq s = apply_seq (aux_seq @ res_seq) s"
        by (simp add: aux_res_seq_def)
      also have "... = apply_seq (aux_seq @ inv_seq aux_seq) s"
        by (simp add: res_is_inverse_aux)
      also have "... = s"
        by (simp add: apply_seq_inv_seq)
      finally show "apply_seq aux_res_seq s = s" .
    qed
  *)


(* Main insertion lemma: inserting any identity sequence preserves apply_seq. *)
lemma insert_identity_preserves:
  assumes "\<forall>s. apply_seq ins s = s"  (* identity sequence *)
  shows   "apply_seq (insert_at k ins xs) s = apply_seq xs s"
  using assms
  by (induct k ins xs arbitrary: s rule: insert_at.induct)
     (auto simp: apply_seq_append)+

lemma invpair_id: "\<forall>s. apply_seq (invpair g) s = s"
  unfolding invpair_def inv_seq_def
  by (intro allI) (simp add: inv_of_cancel)


(* Replace the gate g at the k-th occurrence position with a sequence rep, if it matches. *)
fun replace_at :: "nat \<Rightarrow> gate => gate list => gate list => gate list" where
  "replace_at 0 g rep [] = []"
| "replace_at 0 g rep (x # xs) = (if x = g then rep @ xs else x # xs)"
| "replace_at (Suc n) g rep [] = []"
| "replace_at (Suc n) g rep (x # xs) = x # replace_at n g rep xs"


theorem insert_invpair_preserves:
  "apply_seq (insert_at k (invpair g) xs) s = apply_seq xs s"
  using insert_identity_preserves invpair_id
  by simp


(* Main replacement lemma: replacing g by a rep with same semantics preserves apply_seq. *)
lemma replace_semantics_preserves:
  assumes rep_ok: "\<forall>s. apply_seq rep s = U g s"
  shows "apply_seq (replace_at k g rep xs) s = apply_seq xs s"
  using rep_ok
proof (induct k g rep xs arbitrary: s rule: replace_at.induct)
  case (1 g rep)
  then show ?case by simp
next
  case (2 g rep x xs)
  then show ?case
    by (simp add: apply_seq_append)
next
  case (3 n g rep)
  then show ?case by simp
next
  case (4 n g rep x xs)
  then show ?case by simp
qed



(* Corollary: cloaked replacement preserves semantics, by cloaked_ok assumption. *)
theorem replace_cloaked_preserves:
  "apply_seq (replace_at k g (cloaked g v) xs) s = apply_seq xs s"
  by (rule replace_semantics_preserves, simp add: cloaked_ok)


(* Corollary: delayed replacement preserves semantics, by delayed_ok assumption. *)
theorem replace_delayed_preserves:
  "apply_seq (replace_at k g (delayed g v) xs) s = apply_seq xs s"
  by (rule replace_semantics_preserves, simp add: delayed_ok)

end

end
