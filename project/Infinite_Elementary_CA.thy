section \<open>Infinite Elementary Cellular Automata\<close>

theory Infinite_Elementary_CA
  imports Elementary_CA_Base
begin

type_synonym state = "int \<Rightarrow> cell"

datatype CA = CA (State : state) (Rule : rule)

fun update_state :: "CA \<Rightarrow> state" where
"update_state (CA s r) n = r (Nb (s (n-1)) (s n) (s (n+1)))"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (update_state (CA s r)) r"

fun run :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run ca n = apply_t_times update_CA ca n"

lemma [simp]: "run ca 0 = ca"
apply auto
done

subsection \<open>Properties\<close>

definition stable :: "CA \<Rightarrow> bool" where
"stable ca \<equiv> (\<forall> c. State (update_CA ca) c = (State ca) c)"

(*This def works only because we have binary cells*)
definition uniform :: "state \<Rightarrow> bool" where
"uniform s \<equiv> \<not> (surj s)"

definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s \<equiv> (\<exists> n. State (run A n) = s \<and> n > 0)"

theorem "n>0 \<Longrightarrow> ca yields State (run ca n)"
  apply(simp add: yields_def)
  apply(rule exI)
  apply(rule conjI)
  apply(auto)
done

definition loops :: "CA \<Rightarrow> bool" where
"loops ca \<equiv> ca yields State ca"

lemma "loops ca \<Longrightarrow> (\<exists> n. State (run ca n) = State ca)"
apply auto
apply(simp add: loops_def)
apply(simp add: yields_def)
apply(auto)
done

theorem cycle: "loops ca \<Longrightarrow> (\<exists> m n. (\<forall> k. State (run ca (n + (k*m))) = State ca))"
apply auto
by (metis add_cancel_right_right apply_t_times.simps(1) mult_0 semiring_normalization_rules(7))


fun reversible :: "CA \<Rightarrow> bool" where
"reversible (CA _ r) = (\<forall>s. (\<exists>!s0. State (update_CA (CA s0 r)) = s))"

fun garden_of_eden :: "CA \<Rightarrow> bool" where
"garden_of_eden (CA s r) = (\<not>(\<exists> s0. State (update_CA (CA s0 r)) = s))"

lemma "garden_of_eden ca \<Longrightarrow> \<not>reversible ca"
by (metis garden_of_eden.elims(2) reversible.simps)

(* TODO see if a definition can be made work for infinite compared to finite *)
(*definition orphan :: "state \<Rightarrow> rule \<Rightarrow> bool" where
"orphan s0 r = (\<forall> sl sr. garden_of_eden (CA (sl@s0@sr) r))"*)


definition class1 :: "rule \<Rightarrow> bool" where
"class1 r \<equiv> (\<exists>! f. (\<forall> s. (CA s r) yields f \<and> uniform f \<and> stable (CA f r)))"

definition class2 :: "rule \<Rightarrow> bool" where
"class2 r \<equiv> (\<forall> s. (\<exists> f. (CA s r) yields f \<and> loops (CA f r)))"

lemma "class1 ca \<Longrightarrow> class2 ca"
  using class1_def class2_def loops_def by auto

  
subsection \<open>Example CAs\<close>

definition zero_state :: state where
"zero_state _ \<equiv> Zero"

definition state1 :: state where
"state1 s \<equiv> (if s = 0 then One else Zero)"

definition rule110 :: CA where
"rule110 \<equiv> CA state1 r110"

value "State (run rule110 5) (-3)"

lemma "stable (CA state1 r4)"
apply(simp add: stable_def)
apply auto
by (simp add: state1_def)

(*TODO make lem more interesting by showing a late stage of some rule is uniform*)
lemma "uniform zero_state"
  apply(simp add: zero_state_def uniform_def)
  apply(auto)
done
end
