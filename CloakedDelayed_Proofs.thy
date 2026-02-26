theory CloakedDelayed_Proofs
imports Insertion
begin

(*
  CloakedDelayed_Proofs.thy

  Goal
    Encode the concrete cloaked and delayed replacement recipes as lists of gates,
    then prove that each recipe sequence is semantically equal to the target gate.

  Status
    - Recipes are defined as case splits producing gate list list.
    - cloaked_fun and delayed_fun select a specific recipe by index v.
    - gate_semantics_cd extends gate_semantics with extra equalities that are
      sufficient to prove some recipes (for example HZH = X).
    - The general lemmas cloaked_ok and delayed_ok are still left as sorry.

  Next step
    Discharge cloaked_ok and delayed_ok using a concrete semantics,
    such as the matrix semantics in MatrixSemantics.thy.
*)


(* A table of cloaked recipes: for each target gate g, list all equivalent sequences. *)
definition cloaked_recipes :: "gate \<Rightarrow> gate list list" where
  "cloaked_recipes g =
    (case g of
       X \<Rightarrow> [
         [H, Z, H],
         [S, Y, S, Z],
         [Z, Sdg, Y, Sdg],
         [H, Y, Z, H, Y],
         [Y, H, Z, Y, H],
         [H, Y, H, Y, Sdg, Y, S],
         [Sdg, Y, S, H, Y, H, Y],
         [S, Y, Sdg]
       ]
     | Y \<Rightarrow> [
         [Sdg, X, S],
         [Sdg, X, Z, Sdg],
         [S, Z, X, S]
       ]
     | Z \<Rightarrow> [
         [H, X, H],
         [X, S, Y, S],
         [Sdg, Y, Sdg, X],
         [Y, H, X, Y, H],
         [H, Y, X, H, Y],
         [S, S],
         [T, T, T, T]
       ]
     | S \<Rightarrow> [
         [T, T],
         [Z, T, Z, T],
         [Tdg, Tdg, Z]
       ]
     | _ \<Rightarrow> [])"


(* A table of delayed recipes: same idea, but longer sequences. *)
definition delayed_recipes :: "gate \<Rightarrow> gate list list" where
  "delayed_recipes g =
    (case g of
       X \<Rightarrow> [
         [H, Z, X, H, Z],
         [H, Y, H, Y, Z, X, Z],
         [H, Y, H, X, Y],
         [Y, X, H, Y, H],
         [Z, H, X, Z, H],
         [Z, X, Z, Y, H, Y, H]
       ]
     | Y \<Rightarrow> [
         [X, H, Y, H, X]
       ]
     | Z \<Rightarrow> [
         [H, Y, H, Z, Y],
         [Y, Z, H, Y, H],
         [H, Y, H, Y, X, Z, X],
         [X, Z, X, Y, H, Y, H],
         [X, H, Z, X, H],
         [H, X, Z, H, X],
         [Sdg, Z, S],
         [S, Z, Sdg]
       ]
     | H \<Rightarrow> [
         [X, Z, H, X, Z],
         [Z, X, H, Z, X]
       ]
     | S \<Rightarrow> [
         [Z, T, Sdg, T],
         [Z, Tdg, S, T, Z],
         [H, Y, H, S, X]
       ]
     | T \<Rightarrow> [
         [Z, Sdg, T, S, Z],
         [Z, S, T, Sdg, Z]
       ]
     | _ \<Rightarrow> [])"


(* Select a particular cloaked recipe by index v (0-based). Uses list indexing !. *)
definition cloaked_fun :: "gate \<Rightarrow> nat \<Rightarrow> gate list" where
  "cloaked_fun g v = (cloaked_recipes g) ! v"


(* Select a particular delayed recipe by index v (0-based). *)
definition delayed_fun :: "gate \<Rightarrow> nat \<Rightarrow> gate list" where
  "delayed_fun g v = (delayed_recipes g) ! v"


(*
  gate_semantics_cd
    A temporary extension of gate_semantics where we assume some derived identities
    as axioms (HZH, HXH, SS, TT).

    This is useful to quickly prove small demo lemmas, but the final goal is to
    remove these axioms and derive them from a concrete semantics (matrices).
*)
locale gate_semantics_cd = gate_semantics +
  assumes HZH:  "U H (U Z (U H s)) = U X s"
      and HXH:  "U H (U X (U H s)) = U Z s"
      and SS:   "U S (U S s) = U Z s"
      and TT:   "U T (U T s) = U S s"
begin


(* Example: the first cloaked recipe for X is [H,Z,H]. *)
lemma cloaked_X_0:
  "apply_seq (cloaked_fun X 0) s = U X s"
  unfolding cloaked_fun_def cloaked_recipes_def
  by (simp add: HZH)

lemma cloaked_ok:
  assumes "v < length (cloaked_recipes g)"
  shows "apply_seq (cloaked_fun g v) s = U g s"
  sorry
  (* TODO: replace sorry with a proof using MatrixSemantics, once cloaked_identities is proved. *)

lemma delayed_ok:
  assumes "v < length (delayed_recipes g)"
  shows "apply_seq (delayed_fun g v) s = U g s"
  (* TODO: replace sorry with a proof using MatrixSemantics, once delayed_identities is proved. *)
  sorry

end
end
