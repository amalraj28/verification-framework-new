theory Obfusqate_Insert
  imports Main
begin

datatype gate = H | X | Y | Z | S | Sdg | T | Tdg | Aux | Res

fun inverse :: "gate \<Rightarrow> gate" where
  "inverse H = H"
| "inverse X = X"
| "inverse Y = Y"
| "inverse Z = Z"
| "inverse S = Sdg"
| "inverse Sdg = S"
| "inverse T = Tdg"
| "inverse Tdg = T"
| "inverse Aux = Res"
| "inverse Res = Aux"

locale gate_semantics =
  fixes U :: "gate \<Rightarrow> 's \<Rightarrow> 's"
  assumes inverse_correct: "U (inverse g) (U g s) = s"
begin

fun exec :: "gate list \<Rightarrow> 's \<Rightarrow> 's" where
  "exec [] s = s"
| "exec (g # gs) s = exec gs (U g s)"

lemma exec_append:
  "exec (xs @ ys) s = exec ys (exec xs s)"
  by (induction xs arbitrary: s) simp_all

lemma inverse_pair_is_id:
  "exec [g, inverse g] s = s"
  using inverse_correct
  by simp

lemma idseq_append:
  assumes A: "\<forall>t. exec xs t = t"
  assumes B: "\<forall>t. exec ys t = t"
  shows "\<forall>t. exec (xs @ ys) t = t"
proof
  fix t
  have "exec (xs @ ys) t = exec ys (exec xs t)"
    by (simp add: exec_append)
  also have "... = exec ys t"
    using A by simp
  also have "... = t"
    using B by simp
  finally show "exec (xs @ ys) t = t" .
qed

definition inv_pairs :: "gate list \<Rightarrow> gate list" where
  "inv_pairs gs = concat (map (\<lambda>g. [g, inverse g]) gs)"

lemma inv_pairs_is_id:
  "\<forall>t. exec (inv_pairs gs) t = t"
proof (induction gs)
  case Nil
  then show ?case
    by (simp add: inv_pairs_def)
next
  case (Cons g gs)
  have P1: "\<forall>t. exec [g, inverse g] t = t"
    using inverse_pair_is_id by simp
  have P2: "\<forall>t. exec (inv_pairs gs) t = t"
    using Cons.IH by simp
  show ?case
    using idseq_append[OF P1 P2]
    by (simp add: inv_pairs_def)
qed

lemma insert_identity_preserves:
  assumes idseq: "\<forall>t. exec ins t = t"
  shows "exec (pre @ ins @ post) s = exec (pre @ post) s"
proof -
  have "exec (pre @ ins @ post) s = exec post (exec (pre @ ins) s)"
    by (simp add: exec_append)
  also have "... = exec post (exec ins (exec pre s))"
    by (simp add: exec_append)
  also have "... = exec post (exec pre s)"
    using idseq by simp
  also have "... = exec (pre @ post) s"
    by (simp add: exec_append)
  finally show ?thesis .
qed

lemma replace_gate_preserves:
  assumes equiv: "\<forall>t. exec seq t = U g t"
  shows "exec (pre @ seq @ post) s = exec (pre @ [g] @ post) s"
proof -
  have "exec (pre @ seq @ post) s
        = exec post (exec (pre @ seq) s)"
    by (simp add: exec_append)
  also have "... = exec post (exec seq (exec pre s))"
    by (simp add: exec_append)
  also have "... = exec post (U g (exec pre s))"
    using equiv by simp
  also have "... = exec post (exec [g] (exec pre s))"
    by simp
  also have "... = exec (pre @ [g] @ post) s"
    by (simp add: exec_append)
  finally show ?thesis .
qed

lemma composite_aux_res_is_id:
  "\<forall>t. exec [Aux, Res] t = t"
  using inverse_pair_is_id[of Aux] by simp

lemma inverse_insert_preserves:
  "exec (pre @ inv_pairs gs @ post) s = exec (pre @ post) s"
  using insert_identity_preserves[of "inv_pairs gs" pre post s] inv_pairs_is_id
  by simp

lemma composite_insert_preserves:
  "exec (pre @ [Aux, Res] @ post) s = exec (pre @ post) s"
  using insert_identity_preserves[of "[Aux, Res]" pre post s] composite_aux_res_is_id
  by simp

end

(* ---------------- Strict 1-qubit matrix semantics ---------------- *)

type_synonym vec2 = "complex \<times> complex"

datatype mat2 = Mat2 complex complex complex complex
  (* Mat2 a b c d means [[a,b],[c,d]] *)

definition I2 :: mat2 where
  "I2 = Mat2 1 0 0 1"

definition matmul :: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" (infixl "\<otimes>" 70) where
  "A \<otimes> B =
    (case A of Mat2 a b c d \<Rightarrow>
     case B of Mat2 e f g h \<Rightarrow>
       Mat2 (a*e + b*g) (a*f + b*h)
            (c*e + d*g) (c*f + d*h))"

definition mv :: "mat2 \<Rightarrow> vec2 \<Rightarrow> vec2" where
  "mv A v =
    (case A of Mat2 a b c d \<Rightarrow>
     case v of (x,y) \<Rightarrow> (a*x + b*y, c*x + d*y))"

definition smulM :: "complex \<Rightarrow> mat2 \<Rightarrow> mat2" (infixr "\<cdot>M" 75) where
  "k \<cdot>M A = (case A of Mat2 a b c d \<Rightarrow> Mat2 (k*a) (k*b) (k*c) (k*d))"

definition inv_sqrt2 :: complex where
  "inv_sqrt2 = 1 / sqrt 2"

definition MH :: mat2 where
  "MH = inv_sqrt2 \<cdot>M Mat2 1 1 1 (-1)"

definition MX :: mat2 where "MX = Mat2 0 1 1 0"
definition MZ :: mat2 where "MZ = Mat2 1 0 0 (-1)"
definition MY :: mat2 where "MY = Mat2 0 (-ii) ii 0"

definition MS :: mat2 where "MS = Mat2 1 0 0 ii"
definition MSdg :: mat2 where "MSdg = Mat2 1 0 0 (-ii)"

definition w :: complex where
  "w = cis (pi/4)"  (* exp(i*pi/4) *)

definition MT :: mat2 where "MT = Mat2 1 0 0 w"
definition MTdg :: mat2 where "MTdg = Mat2 1 0 0 (cnj w)"

fun M :: "gate \<Rightarrow> mat2" where
  "M H = MH"
| "M X = MX"
| "M Y = MY"
| "M Z = MZ"
| "M S = MS"
| "M Sdg = MSdg"
| "M T = MT"
| "M Tdg = MTdg"
| "M Aux = I2"   (* placeholder: if you want Aux/Res matrix too, define them here *)
| "M Res = I2"   (* placeholder *)

definition Umat :: "gate \<Rightarrow> vec2 \<Rightarrow> vec2" where
  "Umat g v = mv (M g) v"

end