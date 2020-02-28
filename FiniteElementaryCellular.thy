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

definition width :: "CA \<Rightarrow> nat" where
"width ca = length (State ca)"


(* make provisions for width = 1 *)
(*I think just won't allow*)
(* first is leftmost *)
fun left_update :: "CA \<Rightarrow> cell" where
"left_update ca = (LeftRule ca) ((State ca) ! 0) ((State ca) ! 1)"

(* first is rightmost *)
fun right_update :: "CA \<Rightarrow> cell" where
"right_update ca = (let n = (width ca)-1 in (RightRule ca) ((State ca) ! n) ((State ca) ! (n-1)))"

fun inner_update :: "CA \<Rightarrow> nat \<Rightarrow> cell" where
"inner_update (CA state rule _ _) n = rule (state ! (n-1)) (state ! n) (state ! (n+1))"

fun update_cell :: "CA \<Rightarrow> nat \<Rightarrow> cell" where
"update_cell ca 0 = left_update ca" |
"update_cell ca n = (if n = (width ca) then right_update ca else inner_update ca n)"

(* have to map over indices too!*)
fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA ca = (CA (map (update_cell ca)) (Rule ca) (LeftRule ca) (RightRule ca))"

  










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