section \<open>Toroidal Elementary Cellular Automata\<close>
(*reference damien's cylinders for these *)

theory Toroidal_Elementary_CA
  imports Finite_Elementary_CA_Base
begin


(*fun nbhds :: "state \<Rightarrow> neighbourhood list" where
"nbhds [] = []" | (*this should never happen*)
"nbhds (x#xs) = ((Nb (last xs) x (hd xs)) # (inner_nbhds (x#xs))) @ [Nb (last (butlast xs)) (last xs) x]"*)

fun nbhds :: "state \<Rightarrow> neighbourhood list" where
"nbhds xs = inner_nbhds ((last xs) # xs @ [hd xs])"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map r (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"


subsection \<open> Basic CA Rule Examples \<close>

definition rule110 :: CA where
"rule110 \<equiv> CA [Zero, One, Zero] r110"


subsection \<open>Properties\<close>

definition stable :: "CA \<Rightarrow> bool" where
"stable ca \<equiv> State (update_CA ca) = State ca"

definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s \<equiv> (\<exists> n. State (run_t_steps A n) = s \<and> n > 0)"

definition loops :: "CA \<Rightarrow> bool" where
"loops ca \<equiv> ca yields State ca"

(* TODO reframe in terms of rules only *)
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


(* maybe add some infix notation for this or other things as it looks good *)
fun garden_of_eden :: "CA \<Rightarrow> bool" where
"garden_of_eden (CA s r) = (\<not>(\<exists> s0. State (update_CA (CA s0 r)) = s))"

definition orphan :: "state \<Rightarrow> rule \<Rightarrow> bool" where
"orphan s0 r = (\<forall> sl sr. garden_of_eden (CA (sl@s0@sr) r))"

lemma "garden_of_eden ca \<Longrightarrow> \<not>reversible ca"
  apply (metis garden_of_eden.elims(2) reversible.simps)
done

(*lemma "garden_of_eden (CA s r) \<Longrightarrow> (\<exists> s0. (orphan s0 r) \<and> (\<exists> sl sr. (sl@s0@sr) = s))"*)

definition class1 :: "rule \<Rightarrow> bool" where
"class1 r \<equiv> (\<exists>! f. (\<forall> s. (CA s r) yields f \<and> uniform f \<and> stable (CA f r)))"

definition class2 :: "rule \<Rightarrow> bool" where
"class2 r \<equiv> (\<forall> s. (\<exists> f. (CA s r) yields f \<and> loops (CA f r)))"

lemma "class1 ca \<Longrightarrow> class2 ca"
  using class1_def class2_def loops_def by auto
end
