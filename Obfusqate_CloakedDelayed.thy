theory Obfusqate_CloakedDelayed
  imports Complex_Main
begin

definition Iunit :: complex where
  "Iunit = Complex (0::real) 1"

datatype gate = H | X | Y | Z | S | Sdg | T | Tdg

datatype mat2 = Mat2 complex complex complex complex

definition I2 :: mat2 where
  "I2 = Mat2 1 0 0 1"

definition smulM :: "complex \<Rightarrow> mat2 \<Rightarrow> mat2" where
  "smulM k A =
     (case A of Mat2 a b c d \<Rightarrow>
        Mat2 (k*a) (k*b) (k*c) (k*d))"

definition matmul :: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" where
  "matmul A B =
     (case A of Mat2 a b c d \<Rightarrow>
      case B of Mat2 e f g h \<Rightarrow>
        Mat2 (a*e + b*g)
             (a*f + b*h)
             (c*e + d*g)
             (c*f + d*h))"

definition inv_sqrt2 :: complex where
  "inv_sqrt2 = 1 / sqrt 2"

definition MH :: mat2 where
  "MH = smulM inv_sqrt2 (Mat2 1 1 1 (-1))"

definition MX :: mat2 where
  "MX = Mat2 0 1 1 0"

definition MZ :: mat2 where
  "MZ = Mat2 1 0 0 (-1)"

definition MY :: mat2 where
  "MY = Mat2 0 (-Iunit) Iunit 0"

definition MS :: mat2 where
  "MS = Mat2 1 0 0 Iunit"

definition MSdg :: mat2 where
  "MSdg = Mat2 1 0 0 (-Iunit)"

definition w :: complex where
  "w = cis (pi/4)"

definition MT :: mat2 where
  "MT = Mat2 1 0 0 w"

definition MTdg :: mat2 where
  "MTdg = Mat2 1 0 0 (cnj w)"

definition M :: "gate \<Rightarrow> mat2" where
  "M g =
    (case g of
       H   \<Rightarrow> MH
     | X   \<Rightarrow> MX
     | Y   \<Rightarrow> MY
     | Z   \<Rightarrow> MZ
     | S   \<Rightarrow> MS
     | Sdg \<Rightarrow> MSdg
     | T   \<Rightarrow> MT
     | Tdg \<Rightarrow> MTdg)"

primrec mat_exec :: "gate list \<Rightarrow> mat2" where
  "mat_exec [] = I2"
| "mat_exec (g # gs) = mat_exec gs \<otimes> M g"


(* Convenience simp rules to unfold everything *)
lemmas unfold_all =
  I2_def smulM_def matmul_def inv_sqrt2_def
  MH_def MX_def MY_def MZ_def MS_def MSdg_def
  w_def MT_def MTdg_def

(* Basic facts about cis(pi/4) powers, for strict identities involving T *)
lemma w_sq:
  "w * w = Iunit"
  unfolding w_def
  by (simp add: cis_mult)

lemma w_four:
  "w^4 = -1"
proof -
  have "w^4 = (w*w)^2"
    by (simp add: power2_eq_square power4_eq_xxxx)
  also have "... = (Iunit)^2"
    using w_sq by simp
  also have "... = -1"
    by simp
  finally show ?thesis .
qed

lemma w_conj:
  "cnj w = inverse w"
  unfolding w_def
  by simp

(* ---- Core strict identities (these unlock many recipes) ---- *)

lemma HZH_is_X:
  "mat_exec [H, Z, H] = M X"
  unfolding unfold_all
  (* This proof is arithmetic. simp gets far; field_simp cleans sqrt 2 denominators. *)
  by (simp add: matmul_def smulM_def; field_simp; simp)

lemma HXH_is_Z:
  "mat_exec [H, X, H] = M Z"
  unfolding unfold_all
  by (simp add: matmul_def smulM_def; field_simp; simp)

lemma SS_is_Z:
  "mat_exec [S, S] = M Z"
  unfolding unfold_all
  by (simp add: matmul_def)

lemma TT_is_S:
  "mat_exec [T, T] = M S"
  unfolding unfold_all
  (* Uses w*w = Iunit *)
  using w_sq
  by (simp add: matmul_def)

lemma TTTT_is_Z:
  "mat_exec [T, T, T, T] = M Z"
  unfolding unfold_all
  (* Uses w^4 = -1, diagonal power *)
  using w_four
  by (simp add: matmul_def power4_eq_xxxx)

lemma SdgXS_is_Y:
  "mat_exec [Sdg, X, S] = M Y"
  unfolding unfold_all
  by (simp add: matmul_def)

lemma SXSdg_is_Y:
  "mat_exec [S, X, Sdg] = M Y"
  unfolding unfold_all
  by (simp add: matmul_def)

lemma HZHZXZHH_is_I:
  "mat_exec [H, H, Z, X, Z, X, X, Z, X, Z, H, H] = I2"
  unfolding unfold_all
  by (simp add: matmul_def smulM_def; field_simp; simp)

(* ---- Now prove some of your actual cloaked recipes ---- *)

(* cloaked x: ["h","z","h"] *)
lemma cloaked_x_1:
  "mat_exec [H, Z, H] = M X"
  using HZH_is_X .

(* cloaked z: ["h","x","h"] *)
lemma cloaked_z_1:
  "mat_exec [H, X, H] = M Z"
  using HXH_is_Z .

(* cloaked y: ["sdg","x","s"] *)
lemma cloaked_y_1:
  "mat_exec [Sdg, X, S] = M Y"
  using SdgXS_is_Y .

(* cloaked z: ["s","s"] *)
lemma cloaked_z_2:
  "mat_exec [S, S] = M Z"
  using SS_is_Z .

(* cloaked z: ["t","t","t","t"] *)
lemma cloaked_z_3:
  "mat_exec [T, T, T, T] = M Z"
  using TTTT_is_Z .

(* cloaked s: ["t","t"] *)
lemma cloaked_s_1:
  "mat_exec [T, T] = M S"
  using TT_is_S .

(* delayed z: ["sdg","z","s"] is Z conjugated by S? Here it is actually identity on Z, check strict *)
lemma delayed_z_1:
  "mat_exec [Sdg, Z, S] = M Z"
  unfolding unfold_all
  by (simp add: matmul_def)

lemma delayed_z_2:
  "mat_exec [S, Z, Sdg] = M Z"
  unfolding unfold_all
  by (simp add: matmul_def)

(* delayed h: ["x","z","h","x","z"] equals H *)
lemma delayed_h_1:
  "mat_exec [X, Z, H, X, Z] = M H"
  (* This usually reduces via HZH=X and HXH=Z style, but direct simp also often works *)
  unfolding unfold_all
  by (simp add: matmul_def smulM_def; field_simp; simp)

end