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

fun width :: "CA \<Rightarrow> nat" where
"width ca = length (State ca)"

value "size test"
  










(*typedecl state
consts M :: "(state \<times> state) set"
typedecl "atom"
consts L :: "state \<Rightarrow> atom set"

datatype formula =
  Atom "atom"
  | Neg formula
  | And formula formula
  | AX formula
  | EF formula *)





end