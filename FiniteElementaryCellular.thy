chapter \<open>Finite Cellular Automata\<close>

theory FiniteElementaryCellular
  imports Main
begin

section \<open>Basic definitions of Finite Elementary Cellular Automata\<close>

(* might re-add width if it might help in proofs?*)
datatype cell = One | Zero
(*type_synonym width = nat*)
type_synonym state = "cell list"
type_synonym rule = "cell \<Rightarrow> cell \<Rightarrow> cell \<Rightarrow> cell"
type_synonym edge_rule = "cell \<Rightarrow> cell \<Rightarrow> cell"

(*Width :: width*)
datatype CA = CA (State : state) (Rule : rule) (LeftRule : edge_rule)  (RightRule : edge_rule)

definition null_rule :: rule where
"null_rule _ _ _ = Zero"

definition null_edge :: edge_rule where
"null_edge _ _ = Zero"

definition test :: CA where
"test = CA [One, One, Zero] null_rule null_edge null_edge"

definition width :: "CA \<Rightarrow> nat" where
"width ca = length (State ca)"


(* make provisions for width = 1 *)
(*I think just won't allow*)
(* first is leftmost *)
fun left_update :: "CA \<Rightarrow> cell" where
"left_update ca = (LeftRule ca) ((State ca) ! 0) ((State ca) ! 1)"

(* second is rightmost *)
fun right_update :: "CA \<Rightarrow> cell" where
"right_update ca = (let n = (width ca)-1 in (RightRule ca) ((State ca) ! (n-1)) ((State ca) ! n))"

fun inner_update :: "CA \<Rightarrow> nat \<Rightarrow> cell" where
"inner_update (CA state rule _ _) n = rule (state ! (n-1)) (state ! n) (state ! (n+1))"

fun update_cell :: "CA \<Rightarrow> nat \<Rightarrow> cell" where
"update_cell ca 0 = left_update ca" |
"update_cell ca n = (if n = (width ca) then right_update ca else inner_update ca n)"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA ca = (CA (map (update_cell ca) [0..<width ca]) (Rule ca) (LeftRule ca) (RightRule ca))"

fun apply_t_times :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
"apply_t_times f a 0 = a" |
"apply_t_times f a (Suc n) = apply_t_times f (f a) n"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"

fun left_zero_pad :: "rule \<Rightarrow> cell \<Rightarrow> cell \<Rightarrow> cell" where
"left_zero_pad rule c1 c2 = rule Zero c1 c2"

fun right_zero_pad :: "rule \<Rightarrow> cell \<Rightarrow> cell \<Rightarrow> cell" where
"right_zero_pad rule c2 c1 = rule c2 c1 Zero"

fun rule110 :: rule where
"rule110  One One One = Zero"   |
"rule110  One One Zero = One"   |
"rule110  One Zero One = One"   |
"rule110  One Zero Zero = Zero" |

"rule110  Zero One One = One"   |
"rule110  Zero One Zero = One"  |
"rule110  Zero Zero One = One"  |
"rule110  Zero Zero Zero = Zero"

definition CA110 :: CA where
"CA110 = CA [Zero, Zero, One, Zero] rule110 (left_zero_pad rule110) (right_zero_pad rule110)"

value "run_t_steps CA110 1" 






(*typedecl state
consts M :: "(state \<times> state) set*)
end