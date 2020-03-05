(*chapter \<open>Finite Cellular Automata\<close>*)

(*TODO toroidal 1D CA *)
(*reference damien's cylinders for those *)

theory FiniteElementaryCellular
  imports Main
begin

section \<open>Basic definitions of Finite Elementary Cellular Automata\<close>

(* might re-add width if it might help in proofs?*)
datatype cell = One | Zero
type_synonym state = "cell list"
type_synonym rule = "cell \<Rightarrow> cell \<Rightarrow> cell \<Rightarrow> cell"
type_synonym edge_rule = "cell \<Rightarrow> cell \<Rightarrow> cell"

datatype CA = CA (State : state) (Rule : rule) (LeftRule : edge_rule)  (RightRule : edge_rule)

definition null_rule :: rule where
"null_rule _ _ _ = Zero"

definition null_edge :: edge_rule where
"null_edge _ _ = Zero"

definition testCA :: CA where
"testCA = CA [One, One, Zero] null_rule null_edge null_edge"

definition width :: "CA \<Rightarrow> nat" where
"width ca = length (State ca)"

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
"update_cell ca n = (if n = ((width ca)-1) then right_update ca else inner_update ca n)"



fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA ca = (CA (map (update_cell ca) [0..<width ca]) (Rule ca) (LeftRule ca) (RightRule ca))"

fun apply_t_times :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
"apply_t_times f a 0 = a" |
"apply_t_times f a (Suc n) = apply_t_times f (f a) n"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"


(*definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s = (\<exists> n. State (run_t_steps A n) = s)"*)

definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s \<equiv> (\<exists> n. State (run_t_steps A n) = s \<and> n > 0)"

definition loops :: "CA \<Rightarrow> bool" where
"loops ca \<equiv> ca yields State ca"

definition wellformed :: "CA \<Rightarrow> bool" where
"wellformed ca \<equiv> (width ca \<ge> 3)"

(* maybe add some infix notation for this *)
(* maybe change to run_t_steps 1 for more precision *)
fun garden_of_eden :: "CA \<Rightarrow> bool" where
"garden_of_eden (CA s rule l r) = (\<not>(\<exists> s0. (CA s0 rule l r) yields s))"

fun reversible :: "CA \<Rightarrow> bool" where
"reversible (CA _ rule l r) = (\<forall>s. (\<exists>!s0. State (run_t_steps (CA s0 rule l r) 1) = s))"


(* Only valid for old definition *)
(*theorem "ca yields State ca"
  apply(metis State_def apply_t_times.simps(1) le_boolD order_refl run_t_steps.simps yields_def)
  done*)

theorem "ca yields State (run_t_steps ca 1)"
proof-
  show ?thesis using yields_def by blast
qed

theorem t1 :"n>0 \<Longrightarrow> ca yields State (run_t_steps ca n)"
  apply(simp add: yields_def)
  apply(rule exI)
  apply(rule conjI)
  apply(auto)
  done

theorem
  fixes ca :: CA
  assumes wf : "wellformed ca"
  shows "map (update_cell ca) [0..<width ca] = left_update ca # (map ) @ [right_update ca]"
proof -
qed


theorem "testCA yields [Zero, Zero, Zero]"
  apply(simp add: yields_def)
  apply(rule_tac x=1 in exI)
  apply(rule conjI)
  apply(auto)




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
"CA110 \<equiv> CA [Zero, Zero, Zero, Zero, One] rule110 (left_zero_pad rule110) (right_zero_pad rule110)" 
  
 

end