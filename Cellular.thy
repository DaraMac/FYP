theory Cellular
  imports Main
begin


type_synonym cell_val = bool
type_synonym location = int
type_synonym cell = "location \<times> cell_val "
type_synonym state = "cell list"

(* Rework to only take cell_vals ? *)
type_synonym rule = "cell \<Rightarrow> cell \<Rightarrow> cell \<Rightarrow> cell"
type_synonym cell_autom = "state \<times> rule"

(* Certainly very slow *)
fun cell_lookup :: "location \<Rightarrow> state \<Rightarrow> cell" where
"cell_lookup i [] = (i, False)" |
"cell_lookup i ((l, v)#cs) = (if i = l then (l, v) else cell_lookup i cs)"

fun update_cell :: "cell_autom \<Rightarrow> cell \<Rightarrow> cell" where
"update_cell (s, r) (i, v) = r (cell_lookup (i-1) s) (i, v) (cell_lookup (i+1) s)"

(* does not create new False cells,
  maybe create a function cell_map? *)
fun update_state :: "cell_autom \<Rightarrow> state" where
"update_state (s, r) = map (update_cell (s, r)) s"

(* not getting False cells! *)
fun update_automata :: "cell_autom \<Rightarrow> cell_autom" where
"update_automata (s, r) = ((update_state (s, r)), r)"

fun run_t_steps :: "cell_autom \<Rightarrow> nat \<Rightarrow> cell_autom" where
"run_t_steps ca 0 = ca" |
"run_t_steps ca (Suc n) = run_t_steps (update_automata ca) n"

(* Tests *)

(* Rule 110 *)

fun rule110 :: rule where
"rule110 (_, True) (i, True) (_, True) = (i, False)"   |
"rule110 (_, True) (i, True) (_, False) = (i, True)"   |
"rule110 (_, True) (i, False) (_, True) = (i, True)"   |
"rule110 (_, True) (i, False) (_, False) = (i, False)" |

"rule110 (_, False) (i, True) (_, True) = (i, True)"   |
"rule110 (_, False) (i, True) (_, False) = (i, True)"  |
"rule110 (_, False) (i, False) (_, True) = (i, True)"  |
"rule110 (_, False) (i, False) (_, False) = (i, False)"

fun null_rule :: rule where
"null_rule _ (i, _) _ = (i, False)"

definition start_state :: state where
"start_state = [(-4, False), (-3, False), (-2, False), (-1, False), (0, True), (1, False)]"

definition CA110 :: cell_autom where
"CA110 = (start_state, rule110)"

value "set (fst (run_t_steps CA110 3))"
thm nullity "\<forall> x. set(fst (run_t_steps t null_rule))
end