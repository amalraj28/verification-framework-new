theory MatrixSemantics
  imports Insertion Complex_Main CloakedDelayed_Proofs
begin

(*
  MatrixSemantics.thy

  Goal
    Provide a concrete semantics for the gate datatype using 2x2 complex matrices,
    so that cloaked and delayed recipes can be proved correct by computation.

  Design choice
    mat2 is encoded as a 4-tuple (a,b,c,d) representing [[a,b],[c,d]].
    mat_mul is ordinary matrix multiplication, not tensor product.
    The symbol \<otimes> is reused purely as an infix for readability.

  Status
    - Base matrices for H, X, Y, Z, S, Sdg, T, Tdg are defined.
    - mat_seq evaluates a gate list to a single matrix (right-to-left multiplication).
    - Helper simp sets (gate_simps) and arithmetic lemmas are defined.
    - The big lemma cloaked_identities is currently left inside a comment block,
      because simp is not yet strong enough to close all the generated subgoals.

  Next step
    1) Prove small derived identities as standalone lemmas, for example HZH = X, HXH = Z,
       S*S = Z, T*T = S, and re-use them during recipe proofs.
    2) Alternatively, introduce a normalisation tactic for mat2 expressions and
       use it after expanding mat_mul.
*)


(* A 2x2 complex matrix represented as a 4-tuple (a,b,c,d). *)
type_synonym mat2 = "complex * complex * complex * complex"


(* Identity matrix. *)
definition I2 :: mat2 where
"I2 = (1,0,0,1)"


(* Ordinary 2x2 matrix multiplication. *)
definition mat_mul :: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" (infixl "\<otimes>" 70) where
  "A \<otimes> B = 
  (case A of (a,b,c,d) \<Rightarrow> case B of (e,f,g,h) \<Rightarrow>
    (a*e + b*g, a*f + b*h,
    c*e + d*g, c*f + d*h))"


(* Imaginary unit. Complex_Main already provides \<i>, we alias it to ii. *)
definition ii :: complex where
  "ii = \<i>"


(* Constant 1/sqrt(2) as a complex number (lifted from real). *)
definition inv_sqrt2 :: complex where
  "inv_sqrt2 = of_real (1 / sqrt 2)"


(* Hadamard matrix. *)
definition Hm :: mat2 where
  "Hm = (inv_sqrt2, inv_sqrt2,
         inv_sqrt2, -inv_sqrt2)"


(* Pauli-X matrix. *)
definition Xm :: mat2 where
  "Xm = (0, 1,
         1, 0)"


(* Pauli-Y matrix. *)
definition Ym :: mat2 where
  "Ym = (0, -ii,
         ii, 0)"


(* Pauli-Z matrix. *)
definition Zm :: mat2 where
  "Zm = (1, 0,
         0, -1)"


(* Phase gate S. *)
definition Sm :: mat2 where
  "Sm = (1, 0,
         0, ii)"


(* Inverse phase gate Sdg. *)
definition Sdgm :: mat2 where
  "Sdgm = (1, 0,
          0, -ii)"


(* e^{i pi/4} encoded as (1 + i)/sqrt(2). *)
definition tphase :: complex where
  "tphase = inv_sqrt2 + ii * inv_sqrt2"

definition Tdphase :: complex where
  "Tdphase =  inv_sqrt2 - ii * inv_sqrt2"


(* T gate matrix. *)
definition Tm :: mat2 where
  "Tm = (1, 0,
         0, tphase)"

definition Tdgm :: mat2 where
  "Tdgm = (1, 0,
           0, Tdphase)"
                                

(* Map each primitive gate to its matrix. *)
fun mat_of_gate :: "gate \<Rightarrow> mat2" where
  "mat_of_gate H = Hm"
| "mat_of_gate X = Xm"
| "mat_of_gate Y = Ym"
| "mat_of_gate Z = Zm"
| "mat_of_gate S = Sm"
| "mat_of_gate Sdg = Sdgm"
| "mat_of_gate T = Tm"
| "mat_of_gate Tdg = Tdgm"


(* Evaluate a gate list to a matrix, multiplying from right to left. *)
fun mat_seq :: "gate list \<Rightarrow> mat2" where
  "mat_seq [] = I2"
| "mat_seq (g # gs) = (mat_seq gs) \<otimes> (mat_of_gate g)"
(* This ordering because gates in the list are appended to circuit in same order,
  so when simplified it should be multiplied from right to left.
 *)

lemma mat_mul_I2_left [simp]:
  "I2 \<otimes> A = A"
  unfolding I2_def mat_mul_def
  by (cases A) simp

lemma mat_mul_I2_right [simp]:
  "A \<otimes> I2 = A"
  unfolding I2_def mat_mul_def
  by (cases A) simp

lemma sqrt_times_sqrt:
  fixes x :: real
  assumes "x \<ge> 0"
  shows "of_real (sqrt x) * of_real (sqrt x) = (of_real x :: complex)"
  by (simp add: of_real_mult [symmetric] assms)

term "mat_seq (cloaked_recipes X ! 0)"

lemma debug_HZH:
  "mat_seq [S,Y,S,Z] = mat_of_gate X"
  unfolding mat_seq.simps mat_of_gate.simps
  unfolding I2_def mat_mul_def Sm_def Ym_def Zm_def Xm_def inv_sqrt2_def ii_def
  apply (simp add: sqrt_times_sqrt)
  done
end
