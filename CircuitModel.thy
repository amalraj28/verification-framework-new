theory CircuitModel
  imports Insertion
begin

(*
  CircuitModel.thy

  Goal
    Lift the list-level insertion and replacement reasoning to a simple circuit model
    where each operation is a (gate, wire) pair.

  Model
    op     = Op gate nat         (a single-qubit gate applied to wire q)
    circuit = op list            (a time-ordered list of ops)

  Key results
    - insert_on_wire_identity_preserves:
        inserting an identity gate sequence on a given wire preserves circuit semantics
    - replace_on_wire_*_preserves:
        replacing a gate at a given wire/index by an equivalent sequence preserves semantics
*)


(* A circuit operation is a gate tagged with the wire index it acts on. *)
datatype op = Op gate nat

type_synonym circuit = "op list"


(* All circuit semantics reuse the gate_semantics locale from Insertion.thy. *)
context gate_semantics
begin

(*
  CircuitModel.thy

  Goal
    Lift the list-level insertion and replacement reasoning to a simple circuit model
    where each operation is a (gate, wire) pair.

  Model
    op     = Op gate nat         (a single-qubit gate applied to wire q)
    circuit = op list            (a time-ordered list of ops)

  Key results
    - insert_on_wire_identity_preserves:
        inserting an identity gate sequence on a given wire preserves circuit semantics
    - replace_on_wire_*_preserves:
        replacing a gate at a given wire/index by an equivalent sequence preserves semantics
*)


(* Semantic action of one op: ignore the wire in this abstract model, apply U of the gate. *)
fun apply_op :: "op \<Rightarrow>'s \<Rightarrow>'s" where
  "apply_op (Op g q) s = U g s"


(* Semantic action of a whole circuit: fold apply_op from left to right over the op list. *)
fun apply_circuit :: "circuit \<Rightarrow>'s \<Rightarrow>'s" where
  "apply_circuit [] s = s"
| "apply_circuit (x # xs) s = apply_circuit xs (apply_op x s)"


(* Project out the per-wire gate list from a circuit. Useful for reasoning per wire. *)
fun gates_on_wire :: "nat => circuit => gate list" where
  "gates_on_wire q [] = []"
| "gates_on_wire q (Op g q' # os) =
     (if q = q' then g # gates_on_wire q os else gates_on_wire q os)"


(* Lift a gate list into a circuit fragment by attaching a fixed wire index to each gate. *)
fun lift_on_wire :: "nat => gate list => circuit" where
  "lift_on_wire q [] = []"
| "lift_on_wire q (g # gs) = Op g q # lift_on_wire q gs"


(*
  insert_on_wire_aux
    Walk the circuit and count only occurrences on wire q.
    When the counter reaches i, splice in lift_on_wire q ins at that point.
    cnt is the running counter of how many ops we have seen on wire q so far.
*)
fun insert_on_wire_aux :: "nat => nat => gate list => circuit => nat => circuit" where
  "insert_on_wire_aux q i ins [] cnt =
     (if cnt = i then lift_on_wire q ins else [])"
| "insert_on_wire_aux q i ins (op1 # ops) cnt =
     (case op1 of
        Op g q' =>
          (if q' = q then
             (if cnt = i then lift_on_wire q ins @ (op1 # insert_on_wire_aux q i ins ops (Suc cnt))
              else op1 # insert_on_wire_aux q i ins ops (Suc cnt))
           else op1 # insert_on_wire_aux q i ins ops cnt))"


(* Public wrapper that starts the per-wire counter at 0. *)
definition insert_on_wire :: "nat => nat => gate list => circuit => circuit" where
  "insert_on_wire q i ins c = insert_on_wire_aux q i ins c 0"


(* Executing a lifted fragment is the same as executing the underlying gate sequence. *)
lemma apply_circuit_lift_on_wire:
  "apply_circuit (lift_on_wire q ins) s = apply_seq ins s"
  by (induct ins arbitrary: s) auto


(* Circuit append lemma: semantics of xs @ ys is xs then ys, analogous to apply_seq_append. *)
lemma apply_circuit_append:
  "apply_circuit (xs @ ys) s = apply_circuit ys (apply_circuit xs s)"
  by (induct xs arbitrary: s) auto


(* Core per-wire insertion lemma on circuits, proved by induction on the circuit list. *)
lemma insert_on_wire_aux_identity_preserves:
  assumes id_ins: "\<forall>s. apply_seq ins s = s"
  shows "apply_circuit (insert_on_wire_aux q i ins c cnt) s = apply_circuit c s"
  using id_ins
proof (induct c arbitrary: cnt s)
  case Nil
  then show ?case
    by (simp add: apply_circuit_lift_on_wire)
next
  case (Cons op1 ops)
  then show ?case
  proof (cases op1)
    case (Op g q')
    show ?thesis
    proof (cases "q' = q")
      case False
      then show ?thesis
        using Op Cons
        by simp
    next
      case True
      show ?thesis
      proof (cases "cnt = i")
        case False
        then show ?thesis
          using Op True Cons
          by simp
      next
        case True_cnt: True
        then show ?thesis
          using Op True Cons
          by (simp add: apply_circuit_append apply_circuit_lift_on_wire)
      qed
    qed
  qed
qed


(* The user-facing insertion theorem for circuits (uses the aux lemma plus unfolding). *)
theorem insert_on_wire_identity_preserves:
  assumes id_ins: "\<forall>s. apply_seq ins s = s"
  shows "apply_circuit (insert_on_wire q i ins c) s = apply_circuit c s"
  unfolding insert_on_wire_def
  using insert_on_wire_aux_identity_preserves[OF id_ins]
  by simp


(*
  replace_on_wire_aux
    Similar traversal, but at the i-th gate on wire q:
      - if the encountered gate equals g, replace it by lift_on_wire q rep
      - otherwise leave it untouched
    cnt again counts only ops on wire q.
*)
fun replace_on_wire_aux ::
  "nat => nat => gate => gate list => circuit => nat => circuit" where
  "replace_on_wire_aux q i g rep [] cnt = []"
| "replace_on_wire_aux q i g rep (op1 # ops) cnt =
     (case op1 of
        Op h q' =>
          (if q' = q then
             (if cnt = i then
                (if h = g then lift_on_wire q rep @ replace_on_wire_aux q i g rep ops (Suc cnt)
                 else op1 # replace_on_wire_aux q i g rep ops (Suc cnt))
              else op1 # replace_on_wire_aux q i g rep ops (Suc cnt))
           else op1 # replace_on_wire_aux q i g rep ops cnt))"


(* Public wrapper that starts the per-wire counter at 0. *)
definition replace_on_wire ::
  "nat => nat => gate => gate list => circuit => circuit" where
  "replace_on_wire q i g rep c = replace_on_wire_aux q i g rep c 0"


(* Core per-wire replacement lemma: needs the assumption that rep matches semantics of g. *)
lemma replace_on_wire_aux_preserves:
  assumes rep_ok: "\<forall>s. apply_seq rep s = U g s"
  shows "apply_circuit (replace_on_wire_aux q i g rep c cnt) s =
         apply_circuit c s"
  using rep_ok
proof (induct c arbitrary: cnt s)
  case Nil
  then show ?case by simp
next
  case (Cons op1 ops)
  then show ?case
  proof (cases op1)
    case (Op h q')
    show ?thesis
    proof (cases "q' = q")
      case False
      then show ?thesis
        using Op Cons
        by simp
    next
      case True
      show ?thesis
      proof (cases "cnt = i")
        case False
        then show ?thesis
          using Op True Cons
          by simp
      next
        case True_cnt: True
        show ?thesis
        proof (cases "h = g")
          case False_hg: False
          then show ?thesis
            using Op True True_cnt Cons
            by simp
        next
          case True_hg: True
          then show ?thesis
            using Op True True_cnt Cons
            by (simp add: apply_circuit_append apply_circuit_lift_on_wire)
        qed
      qed
    qed
  qed
qed


(* Wrapper theorem for replacement on circuits. *)
theorem replace_on_wire_preserves:
  assumes rep_ok: "\<forall>s. apply_seq rep s = U g s"
  shows "apply_circuit (replace_on_wire q i g rep c) s = apply_circuit c s"
  unfolding replace_on_wire_def
  using replace_on_wire_aux_preserves[OF rep_ok]
  by simp


(* Instantiate replacement theorem with cloaked, relying on cloaked_ok axiom. *)
theorem replace_on_wire_cloaked_preserves:
  "apply_circuit (replace_on_wire q i g (cloaked g v) c) s = apply_circuit c s"
  by (rule replace_on_wire_preserves) (simp add: cloaked_ok)


(* Instantiate replacement theorem with delayed, relying on delayed_ok axiom. *)
theorem replace_on_wire_delayed_preserves:
  "apply_circuit (replace_on_wire q i g (delayed g v) c) s = apply_circuit c s"
  by (rule replace_on_wire_preserves) (simp add: delayed_ok)

end
end
