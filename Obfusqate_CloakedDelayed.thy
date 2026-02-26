theory Obfusqate_CloakedDelayed
  imports Complex_Main
begin

(* --- Matrix Definitions --- *)

datatype mat2 = Mat2 complex complex complex complex

definition I2 :: mat2 where
  "I2 = Mat2 1 0 0 1"

definition matmul :: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" (infixl "\<otimes>" 70) where
  "matmul A B =
     (case A of Mat2 a b c d \<Rightarrow>
      case B of Mat2 e f g h \<Rightarrow>
        Mat2 (a*e + b*g) (a*f + b*h)
             (c*e + d*g) (c*f + d*h))"

definition smulM :: "complex \<Rightarrow> mat2 \<Rightarrow> mat2" (infixr "\<cdot>M" 75) where
  "smulM k A =
     (case A of Mat2 a b c d \<Rightarrow>
        Mat2 (k*a) (k*b) (k*c) (k*d))"

definition inv_sqrt2 :: complex where
  "inv_sqrt2 = Complex (1 / sqrt 2) 0"

definition i_unit :: complex where
  "i_unit = Complex 0 1"

definition MH :: mat2 where "MH = inv_sqrt2 \<cdot>M Mat2 1 1 1 (-1)"
definition MX :: mat2 where "MX = Mat2 0 1 1 0"
definition MZ :: mat2 where "MZ = Mat2 1 0 0 (-1)"
definition MY :: mat2 where "MY = Mat2 0 (-i_unit) i_unit 0"
definition MS :: mat2 where "MS = Mat2 1 0 0 i_unit"
definition MSdg :: mat2 where "MSdg = Mat2 1 0 0 (-i_unit)"

definition w :: complex where "w = cis (pi/4)"
definition MT :: mat2 where "MT = Mat2 1 0 0 w"
definition MTdg :: mat2 where "MTdg = Mat2 1 0 0 (cnj w)"

datatype gate = H | X | Y | Z | S | Sdg | T | Tdg

fun M :: "gate \<Rightarrow> mat2" where
  "M H = MH" | "M X = MX" | "M Y = MY" | "M Z = MZ"
| "M S = MS" | "M Sdg = MSdg" | "M T = MT" | "M Tdg = MTdg"

(* --- Execution --- *)

primrec mat_exec :: "gate list \<Rightarrow> mat2" where
  "mat_exec [] = I2"
| "mat_exec (g # gs) = mat_exec gs \<otimes> M g"

(* --- Preservation Theorem (The "Point 2") --- *)

type_synonym state = "complex \<times> complex"

definition mv :: "mat2 \<Rightarrow> state \<Rightarrow> state" where
  "mv A v = (case A of Mat2 a b c d \<Rightarrow> case v of (x,y) \<Rightarrow> (a*x + b*y, c*x + d*y))"

definition exec :: "gate list \<Rightarrow> state \<Rightarrow> state" where
  "exec gs s = mv (mat_exec gs) s"

lemma mat_exec_append: "mat_exec (xs @ ys) = mat_exec ys \<otimes> mat_exec xs"
  by (induction xs) (auto simp add: matmul_def case_prod_beta split: mat2.split)

lemma matmul_assoc: "A \<otimes> (B \<otimes> C) = (A \<otimes> B) \<otimes> C"
  unfolding matmul_def by (auto simp add: algebra_simps case_prod_beta split: mat2.split)

theorem replace_equivalent_preserves:
  assumes "mat_exec seq = M g"
  shows "exec (pre @ seq @ post) s = exec (pre @ [g] @ post) s"
proof -
  have "\<forall>A B v. mv (A \<otimes> B) v = mv A (mv B v)"
    unfolding mv_def matmul_def by (auto simp add: algebra_simps case_prod_beta split: mat2.split)
  hence E: "\<forall>xs ys s. exec (xs @ ys) s = exec ys (exec xs s)"
    unfolding exec_def by (simp add: mat_exec_append)
  
  have "exec (pre @ seq @ post) s = exec post (exec seq (exec pre s))"
    by (simp add: E)
  also have "... = exec post (mv (M g) (exec pre s))"
    using assms unfolding exec_def by simp
  also have "... = exec (pre @ [g] @ post) s"
    unfolding exec_def E by simp
  finally show ?thesis .
qed

(* --- Concrete Recipes Proofs (Point 2 Evidence) --- *)

lemma HZH_is_X: "mat_exec [H, Z, H] = M X"
  by (simp add: MH_def MZ_def MX_def matmul_def smulM_def inv_sqrt2_def complex_eq_iff)

lemma HXH_is_Z: "mat_exec [H, X, H] = M Z"
  by (simp add: MH_def MX_def MZ_def matmul_def smulM_def inv_sqrt2_def complex_eq_iff)

lemma SS_is_Z: "mat_exec [S, S] = M Z"
  by (simp add: MS_def MZ_def matmul_def complex_eq_iff i_unit_def)

lemma TT_is_S: "mat_exec [T, T] = M S"
  unfolding MT_def MS_def mat_exec.simps matmul_def I2_def
  by (simp add: complex_eq_iff i_unit_def w_def cis_mult)

lemma TTTT_is_Z: "mat_exec [T, T, T, T] = M Z"
proof -
  have "w * w = i_unit" by (simp add: w_def i_unit_def cis_mult)
  hence "w * w * w * w = -1" by (simp add: i_unit_def)
  thus ?thesis
    unfolding MT_def MZ_def mat_exec.simps matmul_def I2_def
    by (simp add: complex_eq_iff)
qed

lemma SdgXS_is_Y: "mat_exec [Sdg, X, S] = M Y"
  by (simp add: MSdg_def MX_def MS_def MY_def matmul_def complex_eq_iff i_unit_def)

(* Proof of a more complex one from sequences.py: cloaked x Variant 3 ["z", "sdg", "y", "sdg"]? 
   Wait, sequences.py said "z": ["sdg", "y", "sdg", "x"] 
*)
lemma cloaked_z_variant: "mat_exec [Sdg, Y, Sdg, X] = M Z"
  by (simp add: MSdg_def MY_def MX_def MZ_def matmul_def complex_eq_iff i_unit_def)

end