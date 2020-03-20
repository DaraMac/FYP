(*reference damien's cylinders for these *)

theory ToroidalElementaryCellular
  imports Main
begin

section \<open>Basic definitions of Toroidal Elementary Cellular Automata\<close>

(* factor out the core essentials to both the 1D CA *)

(* perhaps typeclass them so well-formed works on both! *)

(* maybe rename so I can compare them but probably not necessary! *)

datatype cell = One | Zero
type_synonym state = "cell list"
type_synonym rule = "cell \<Rightarrow> cell \<Rightarrow> cell \<Rightarrow> cell"

datatype CA = CA (State : state) (Rule : rule)

(* Generate the neighbourhoods for each cell *)
(* TODO this is the only function that needs to change to make different topologies!*)

(* maybe define neighbourhoods as a type? *)
(* still easy enough to work with, or just a tuple? *)
fun inner_nbhds :: "state \<Rightarrow> state list" where
"inner_nbhds (x#y#z#[]) = [x, y, z] # []" |
"inner_nbhds (x#y#z#zs) = [x,y,z] # (inner_nbhds (y#z#zs))" |
"inner_nbhds _ = []" (* neighbourhoods aren't defined for \<le> 2 *)

fun nbhds :: "state \<Rightarrow> state list" where
"nbhds [] = []" | (*this should never happen*)
"nbhds (x#xs) = (((last xs)#x#[hd xs]) # (inner_nbhds (x#xs))) @ [(last (butlast xs))#(last xs)#[x]]"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map update_cell (nbhds s)) r"
end