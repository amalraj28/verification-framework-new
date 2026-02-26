theory Quantum_Obfuscation_Verification
  imports Complex_Main
begin

(* --- 1. Basic Definitions --- *)

datatype gate = H | X | Y | Z | S | Sdg | T | Tdg | Aux | Res

type_synonym state = "complex \<times> complex"

datatype mat2 = Mat2 complex complex complex complex

definition I2 :: mat2 where
  "I2 = Mat2 1 0 0 1"

definition smulM :: "complex \<Rightarrow> mat2 \<Rightarrow> mat2" (infixr "\<cdot>M" 75) where
  "k \<cdot>M A = (case A of Mat2 a b c d \<Rightarrow> Mat2 (k*a) (k*b) (k*c) (k*d))"

definition matmul :: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" (infixl "\<otimes>" 70) where
  "A \<otimes> B =
    (case A of Mat2 a b c d \<Rightarrow>
     case B of Mat2 e f g h \<Rightarrow>
       Mat2 (a*e + b*g) (a*f + b*h)
            (c*e + d*g) (c*f + d*h))"

definition mv :: "mat2 \<Rightarrow> state \<Rightarrow> state" where
  "mv A v = (case A of Mat2 a b c d \<Rightarrow> case v of (x,y) \<Rightarrow> (a*x + b*y, c*x + d*y))"

(* --- 2. Gate Matrices --- *)

definition inv_sqrt2 :: complex where
  "inv_sqrt2 = Complex (1 / sqrt 2) 0"

definition i_unit :: complex where
  "i_unit = Complex 0 1"

definition MH :: mat2 where "MH = inv_sqrt2 \<cdot>M (Mat2 1 1 1 (-1))"
definition MX :: mat2 where "MX = Mat2 0 1 1 0"
definition MY :: mat2 where "MY = Mat2 0 (-i_unit) i_unit 0"
definition MZ :: mat2 where "MZ = Mat2 1 0 0 (-1)"
definition MS :: mat2 where "MS = Mat2 1 0 0 i_unit"
definition MSdg :: mat2 where "MSdg = Mat2 1 0 0 (-i_unit)"

definition w_unit :: complex where
  "w_unit = cis (pi/4)"

definition MT :: mat2 where "MT = Mat2 1 0 0 w_unit"
definition MTdg :: mat2 where "MTdg = Mat2 1 0 0 (cnj w_unit)"

(* Composite gates as defined in sequences.py *)
(* Aux = H H Z X Z X, Res = X Z X Z H H *)
definition MAux :: mat2 where "MAux = MX \<otimes> MZ \<otimes> MX \<otimes> MZ \<otimes> MH \<otimes> MH"
definition MRes :: mat2 where "MRes = MH \<otimes> MH \<otimes> MZ \<otimes> MX \<otimes> MZ \<otimes> MX"

fun M :: "gate \<Rightarrow> mat2" where
  "M H = MH"
| "M X = MX"
| "M Y = MY"
| "M Z = MZ"
| "M S = MS"
| "M Sdg = MSdg"
| "M T = MT"
| "M Tdg = MTdg"
| "M Aux = MAux"
| "M Res = MRes"

(* --- 3. Sequence Execution --- *)

primrec mat_exec :: "gate list \<Rightarrow> mat2" where
  "mat_exec [] = I2"
| "mat_exec (g # gs) = mat_exec gs \<otimes> M g"

definition exec :: "gate list \<Rightarrow> state \<Rightarrow> state" where
  "exec gs s = mv (mat_exec gs) s"

(* --- 4. High-level Properties --- *)

lemma mat_exec_append:
  "mat_exec (xs @ ys) = mat_exec ys \<otimes> mat_exec xs"
  by (induction xs) (simp_all add: matmul_def case_prod_beta)

(* Wait, matmul is associative? Yes. *)
lemma matmul_assoc: "A \<otimes> (B \<otimes> C) = (A \<otimes> B) \<otimes> C"
  unfolding matmul_def by (auto simp add: algebra_simps case_prod_beta split: mat2.split)

lemma mat_exec_append_fixed:
  "mat_exec (xs @ ys) = mat_exec ys \<otimes> mat_exec xs"
proof (induction xs)
  case Nil
  then show ?case by (simp add: matmul_def I2_def case_prod_beta split: mat2.split)
next
  case (Cons a xs)
  then show ?case by (simp add: matmul_assoc)
qed

lemma exec_append:
  "exec (xs @ ys) s = exec ys (exec xs s)"
proof -
  have "mv (mat_exec ys \<otimes> mat_exec xs) s = mv (mat_exec ys) (mv (mat_exec xs) s)"
    unfolding mv_def matmul_def by (auto simp add: algebra_simps case_prod_beta split: mat2.split)
  then show ?thesis
    unfolding exec_def by (simp add: mat_exec_append_fixed)
qed

(* --- 5. Preservation Theorems --- *)

theorem insert_identity_preserves:
  assumes "mat_exec ins = I2"
  shows "exec (pre @ ins @ post) s = exec (pre @ post) s"
proof -
  have "exec (pre @ ins @ post) s = exec post (exec ins (exec pre s))"
    by (simp add: exec_append)
  also have "... = exec post (mv I2 (exec pre s))"
    using assms unfolding exec_def by simp
  also have "... = exec post (exec pre s)"
    unfolding mv_def I2_def by (auto simp add: case_prod_beta)
  also have "... = exec (pre @ post) s"
    by (simp add: exec_append)
  finally show ?thesis .
qed

theorem replace_equivalent_preserves:
  assumes "mat_exec seq = M g"
  shows "exec (pre @ seq @ post) s = exec (pre @ [g] @ post) s"
proof -
  have "exec (pre @ seq @ post) s = exec post (exec seq (exec pre s))"
    by (simp add: exec_append)
  also have "... = exec post (mv (M g) (exec pre s))"
    using assms unfolding exec_def by simp
  also have "... = exec post (exec [g] (exec pre s))"
    unfolding exec_def by simp
  also have "... = exec (pre @ [g] @ post) s"
    by (simp add: exec_append)
  finally show ?thesis .
qed

(* --- 6. Verification of Techniques --- *)

(* 6.1. Inverse Gates *)
fun inverse_gate :: "gate \<Rightarrow> gate" where
  "inverse_gate H = H"
| "inverse_gate X = X"
| "inverse_gate Y = Y"
| "inverse_gate Z = Z"
| "inverse_gate S = Sdg"
| "inverse_gate Sdg = S"
| "inverse_gate T = Tdg"
| "inverse_gate Tdg = T"
| "inverse_gate Aux = Res"
| "inverse_gate Res = Aux"

lemma MH_inv [simp]: "MH \<otimes> MH = I2"
  unfolding MH_def inv_sqrt2_def matmul_def smulM_def I2_def
  by (simp add: complex_eq_iff)

lemma MX_inv [simp]: "MX \<otimes> MX = I2"
  unfolding MX_def matmul_def I2_def by simp

lemma MY_inv [simp]: "MY \<otimes> MY = I2"
  unfolding MY_def matmul_def I2_def by simp

lemma MZ_inv [simp]: "MZ \<otimes> MZ = I2"
  unfolding MZ_def matmul_def I2_def by simp

lemma MS_inv [simp]: "MSdg \<otimes> MS = I2" "MS \<otimes> MSdg = I2"
  unfolding MS_def MSdg_def matmul_def I2_def by simp_all

lemma MT_inv [simp]: "MTdg \<otimes> MT = I2" "MT \<otimes> MTdg = I2"
  unfolding MT_def MTdg_def matmul_def I2_def
  by (simp_all add: complex_eq_iff)

lemma MAux_Res_inv [simp]: "MRes \<otimes> MAux = I2"
  unfolding MRes_def MAux_def
  by (simp add: matmul_assoc)

lemma mat_exec_inv_pair:
  "mat_exec [g, inverse_gate g] = I2"
  by (cases g) (simp_all add: matmul_assoc)

theorem inverse_insertion_correct:
  "exec (pre @ [g, inverse_gate g] @ post) s = exec (pre @ post) s"
  using insert_identity_preserves mat_exec_inv_pair by blast

(* 6.2. Composite Gates *)
lemma composite_sequence_correct:
  "mat_exec [Aux, Res] = I2"
  unfolding MRes_def MAux_def
  by (simp add: matmul_assoc)

theorem composite_insertion_correct:
  "exec (pre @ [Aux, Res] @ post) s = exec (pre @ post) s"
  using insert_identity_preserves composite_sequence_correct by blast

(* 6.3. Cloaked Gates (Examples) *)
lemma cloaked_x_recipe1_correct:
  "mat_exec [H, Z, H] = M X"
  by (simp add: MH_def MZ_def MX_def matmul_def smulM_def inv_sqrt2_def complex_eq_iff)

lemma cloaked_z_recipe2_correct:
  "mat_exec [S, S] = M Z"
  by (simp add: MS_def MZ_def matmul_def i_unit_def complex_eq_iff)

theorem cloaked_x_preservation:
  "exec (pre @ [H, Z, H] @ post) s = exec (pre @ [X] @ post) s"
  by (rule replace_equivalent_preserves[OF cloaked_x_recipe1_correct])

end
