section \<open> Cellular Automata Base\<close>

theory CA_Base
  imports Main
begin

datatype cell = Zero | One

fun flip :: "cell \<Rightarrow> cell" where
"flip One = Zero" |
"flip Zero = One"

fun apply_t_times :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
"apply_t_times f a 0 = a" |
"apply_t_times f a (Suc n) = apply_t_times f (f a) n"


lemma flip_cancel [simp]:"flip (flip c) = c"
apply(induction c)
apply(auto)
done

lemma apply_once [simp]: "apply_t_times f a 1 = (f a)"
apply(auto)
done

end
