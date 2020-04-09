theory Finite_TwoDim_CA_Base
  imports TwoDim_CA_Base
begin

type_synonym state = "cell list list"

datatype CA = CA (State : state) (Rule : rule)

definition width :: "state \<Rightarrow> nat" where
"width s \<equiv> length s"

definition height :: "state \<Rightarrow> nat" where
"height s = length (hd s)"


definition oneCentre :: state where
"oneCentre \<equiv> [[Zero, Zero, Zero], [Zero, One, Zero], [Zero, Zero, Zero]]"

fun get_cell :: "state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> cell" where
"get_cell s x y = s!(nat x)!(nat y)"

value "[(nat (1+i) mod 3, nat (1+j) mod 3). j\<leftarrow>rev [-1..1], i\<leftarrow>[-1..1]]"

fun get_nbhd :: "state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> neighbourhood" where
"get_nbhd s x y = (let w = int (width s) in (let h = int (height s) in
 list_to_nb [get_cell s ((x+i) mod w) ((y+j) mod h). j \<leftarrow> rev [-1..1], i \<leftarrow> [-1..1]]))"

fun nbhds :: "state \<Rightarrow> neighbourhood list list" where
"nbhds s = (let h = int ((height s)-1) in (let w = int ((width s)-1) in
 [[get_nbhd s x y. y \<leftarrow> [0..h]]. x \<leftarrow> [0..w]]))"

 
fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map (\<lambda> xs. map r xs) (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"


definition blinker :: state where
"blinker \<equiv> [replicate 5 Zero,
 [Zero ,Zero, One, Zero, Zero],
 [Zero, Zero, One, Zero, Zero],
 [Zero, Zero, One, Zero, Zero],
 replicate 5 Zero]"


subsection \<open>Simple properties for CA\<close>

definition widthCA :: "CA \<Rightarrow> nat" where
"widthCA ca = width (State ca)"

definition heightCA :: "CA \<Rightarrow> nat" where
"heightCA ca = height (State ca)"

definition wellformed :: "state \<Rightarrow> bool" where
"wellformed s \<equiv> (width s \<ge> 3) \<and> (height s \<ge> 3) \<and> (\<forall> i. length (s ! (i mod (width s))) = height s)"

(* doesnt work for 2D currently *)
definition uniform :: "state \<Rightarrow> bool" where
"uniform s \<equiv> length (remdups s) = 1"
end