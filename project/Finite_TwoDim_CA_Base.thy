section \<open>Finite 2D Cellular Automata Base\<close>

theory Finite_TwoDim_CA_Base
  imports TwoDim_CA_Base
begin
  
(* TODO uniform *)
type_synonym state = "cell list list"

datatype CA = CA (State : state) (Rule : rule)


subsection \<open>Simple properties for CA\<close>

definition width :: "state \<Rightarrow> nat" where
"width s \<equiv> length s"

definition height :: "state \<Rightarrow> nat" where
"height s = length (hd s)"

definition int_width :: "state \<Rightarrow> int" where
"int_width s \<equiv> int (width s)"

definition int_height :: "state \<Rightarrow> int" where
"int_height s \<equiv> int (height s)"

definition widthCA :: "CA \<Rightarrow> nat" where
"widthCA ca = width (State ca)"

definition heightCA :: "CA \<Rightarrow> nat" where
"heightCA ca = height (State ca)"

definition wellformed :: "state \<Rightarrow> bool" where
"wellformed s \<equiv> (width s \<ge> 3) \<and> (height s \<ge> 3) \<and> (\<forall> i. length (s ! (i mod (width s))) = height s)"

(* doesnt work for 2D currently *)
definition uniform :: "state \<Rightarrow> bool" where
"uniform s \<equiv> length (remdups s) = 1"

definition oneCentre :: state where
"oneCentre \<equiv> [[Zero, Zero, Zero], [Zero, One, Zero], [Zero, Zero, Zero]]"

definition offCentre :: state where
"offCentre \<equiv> [[One, Zero, Zero], [Zero, Zero, Zero], [Zero, Zero, Zero]]"

definition toroidalBlinker :: state where
"toroidalBlinker \<equiv>
 [replicate 5 Zero,
 [Zero ,Zero, One, Zero, Zero],
 [Zero, Zero, One, Zero, Zero],
 [Zero, Zero, One, Zero, Zero],
 replicate 5 Zero]"

definition boundedBlinker :: state where
"boundedBlinker \<equiv> [
                    [Zero, One, Zero],
                    [Zero, One, Zero],
                    [Zero, One, Zero]
                   ]"
end
