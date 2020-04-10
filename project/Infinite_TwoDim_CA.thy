section \<open>Infinite 2D Cellular Automata\<close>

theory Infinite_TwoDim_CA
  imports TwoDim_CA_Base
begin
  
type_synonym state = "int \<Rightarrow> int \<Rightarrow> cell"

datatype CA = CA (State : state) (Rule : rule)

(*could this be written nicer? maybe a calculate neighbourhood function*)
fun update_state :: "CA \<Rightarrow> state" where
"update_state (CA s r) x y = r (Nb (s (x-1) (y+1)) (s x (y+1)) (s (x+1) (y+1))
                                   (s (x-1)  y)    (s x  y)    (s (x+1)  y)
                                   (s (x-1) (y-1)) (s x (y-1)) (s (x+1) (y-1)))"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (update_state (CA s r)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"


subsection \<open>Properties\<close>

definition stable :: "CA \<Rightarrow> bool" where
"stable ca \<equiv> State (update_CA ca) = State ca"

(*This def works only because we have binary cells*)
definition uniform :: "state \<Rightarrow> bool" where
"uniform s \<equiv> \<not> (surj s)"

definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s \<equiv> (\<exists> n. State (run_t_steps A n) = s \<and> n > 0)"

definition loops :: "CA \<Rightarrow> bool" where
"loops ca \<equiv> ca yields State ca"

fun reversible :: "CA \<Rightarrow> bool" where
"reversible (CA _ r) = (\<forall>s. (\<exists>!s0. State (update_CA (CA s0 r)) = s))"

fun garden_of_eden :: "CA \<Rightarrow> bool" where
"garden_of_eden (CA s r) = (\<not>(\<exists> s0. State (update_CA (CA s0 r)) = s))"

lemma "garden_of_eden ca \<Longrightarrow> \<not>reversible ca"
  by (metis garden_of_eden.elims(2) reversible.simps)


definition class1 :: "rule \<Rightarrow> bool" where
"class1 r \<equiv> (\<exists>! f. (\<forall> s. (CA s r) yields f \<and> uniform f \<and> stable (CA f r)))"

definition class2 :: "rule \<Rightarrow> bool" where
"class2 r \<equiv> (\<forall> s. (\<exists> f. (CA s r) yields f \<and> loops (CA f r)))"

lemma "class1 ca \<Longrightarrow> class2 ca"
  using class1_def class2_def loops_def by auto

subsection \<open>Concrete examples\<close>

definition oneCentre :: state where
"oneCentre x y = (if x=0 \<and> y=0 then One else Zero)"

definition blinker :: state where
"blinker x y = (if x=0 \<and> (y=-1 \<or> y=0 \<or> y=1)
                then One else Zero)"

definition lifeBlinker :: CA where
"lifeBlinker \<equiv> CA blinker life"

value "State (run_t_steps lifeBlinker 0) (0) (0)"

(*lemma "State (run_t_steps lifeBlinker n) 0 0 = One"
apply(simp add: lifeBlinker_def)*)
end
