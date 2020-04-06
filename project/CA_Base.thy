chapter \<open>Cellular Automata Basics\<close>

theory CA_Base
  imports Main
begin


datatype cell = Zero | One

datatype neighbourhood = Nb cell cell cell
type_synonym rule = "neighbourhood \<Rightarrow> cell"

end