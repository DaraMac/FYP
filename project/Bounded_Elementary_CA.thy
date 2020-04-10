section \<open>Bounded Elementary Cellular Automata\<close>

theory Bounded_Elementary_CA
  imports Finite_Elementary_CA_Base
begin

subsection \<open>Basic definitions of Finite Elementary Cellular Automata\<close>
(* Going to go with left/right boundaries as Zero by default *)
(* Might like that to be flexible somehow? Without ruining CA type def*)

(* doesnt need wellformed anymore!*)
fun nbhds :: "state \<Rightarrow> neighbourhood list" where
"nbhds [] = []" | (*this should never happen*)
"nbhds (x#[]) = [(Nb Zero x Zero)]" |
"nbhds (x#y#[]) = [(Nb Zero x y), (Nb x y Zero)]" |
"nbhds (x#xs) = ((Nb Zero x (hd xs)) # (inner_nbhds (x#xs))) @ [Nb (last (butlast xs)) (last xs) Zero]"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map r (nbhds s)) r"

fun run :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run ca n = apply_t_times update_CA ca n"


subsection \<open>Properties\<close>

definition stable :: "CA \<Rightarrow> bool" where
"stable ca \<equiv> State (update_CA ca) = State ca"

definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s \<equiv> (\<exists> n. State (run A n) = s \<and> n > 0)"

definition loops :: "CA \<Rightarrow> bool" where
"loops ca \<equiv> ca yields State ca"

(* maybe add some infix notation for this *)
(* maybe change to run_t_steps 1 for more precision *)
fun garden_of_eden :: "CA \<Rightarrow> bool" where
"garden_of_eden (CA s r) = (\<not>(\<exists> s0. (CA s0 r) yields s))"

fun reversible :: "CA \<Rightarrow> bool" where
"reversible (CA _ r) = (\<forall>s. (\<exists>!s0. State (update_CA (CA s0 r)) = s))"

theorem "ca yields State (run ca 1)"
proof-
  show ?thesis using yields_def by blast
qed

theorem t1 :"n>0 \<Longrightarrow> ca yields State (run ca n)"
  apply(simp add: yields_def)
  apply(rule exI)
  apply(rule conjI)
  apply(auto)
  done


definition orphan :: "state \<Rightarrow> rule \<Rightarrow> bool" where
"orphan s0 r = (\<forall> sl sr. garden_of_eden (CA (
sl@s0@sr) r))"

(* TODO find out why this doesnt work but all others do*)
(*lemma "garden_of_eden ca \<Longrightarrow> \<not>reversible ca"*)


definition class1 :: "rule \<Rightarrow> bool" where
"class1 r \<equiv> (\<exists>! f. (\<forall> s. (CA s r) yields f \<and> uniform f \<and> stable (CA f r)))"

definition class2 :: "rule \<Rightarrow> bool" where
"class2 r \<equiv> (\<forall> s. (\<exists> f. (CA s r) yields f \<and> loops (CA f r)))"

lemma "class1 ca \<Longrightarrow> class2 ca"
  using class1_def class2_def loops_def by auto
end
