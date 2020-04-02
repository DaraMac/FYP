(*chapter \<open>Finite Cellular Automata\<close>*)

(*reference damien's cylinders for those *)

theory FiniteElementaryCellular
  imports Main CellularBase
begin

section \<open>Basic definitions of Finite Elementary Cellular Automata\<close>
(* Going to go with left/right boundaries as Zero by default *)
(* Might like that to be flexible somehow? Without ruining CA type def*)

(*
(* might re-add width on a type level if it might help in proofs?*)
datatype cell = One | Zero
type_synonym state = "cell list"
type_synonym rule = "cell \<Rightarrow> cell \<Rightarrow> cell \<Rightarrow> cell"
type_synonym edge_rule = "cell \<Rightarrow> cell \<Rightarrow> cell"

(* could merge all rules into one compositite type *)
datatype CA = CA (State : state) (Rule : rule) (LeftRule : edge_rule)  (RightRule : edge_rule)



definition null_edge :: edge_rule where
"null_edge _ _ = Zero"
*)

(*
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
"update_cell ca n = (if n = ((width ca)-1) then right_update ca else inner_update ca n)"*)

(*fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA ca = (CA (map (update_cell ca) [0..<width ca]) (Rule ca) (LeftRule ca) (RightRule ca))"*)

fun nbhds :: "state \<Rightarrow> neighbourhood list" where
"nbhds [] = []" | (*this should never happen*)
"nbhds (x#xs) = ((Nb Zero x (hd xs)) # (inner_nbhds (x#xs))) @ [Nb (last (butlast xs)) (last xs) Zero]"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map r (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"

definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s \<equiv> (\<exists> n. State (run_t_steps A n) = s \<and> n > 0)"

definition loops :: "CA \<Rightarrow> bool" where
"loops ca \<equiv> ca yields State ca"

(* maybe add some infix notation for this *)
(* maybe change to run_t_steps 1 for more precision *)
fun garden_of_eden :: "CA \<Rightarrow> bool" where
"garden_of_eden (CA s r) = (\<not>(\<exists> s0. (CA s0 r) yields s))"

fun reversible :: "CA \<Rightarrow> bool" where
"reversible (CA _ r) = (\<forall>s. (\<exists>!s0. State (update_CA (CA s0 r)) = s))"

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


theorem "testCA yields [Zero, Zero, Zero]"
  apply(simp add: yields_def)
  apply(rule_tac x=1 in exI)
  apply(rule conjI)
   apply(auto)
  sorry
end