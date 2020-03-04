theory test
  imports Main Complex_Main
begin


fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n"
|"add (Suc m) n = Suc(add m n)"

lemma add_0 [simp]: "add m 0 = m"
  apply(induction m)
  apply(auto)
  done

lemma add_associates [simp]: "add (add a b) c = add a (add b c)"
  apply(induction a)
  apply(auto)
  done

lemma l2 [simp]: "add m (Suc n) = Suc (add m n)"
  apply(induction m)
  apply(auto)
 done

lemma add_commutes [simp]: "add m n = add n m"
  apply(induction m)
  apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc (Suc (double m))"

lemma l3 [simp]: "double m = add m m"
  apply(induction m)
  apply(auto)
done

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count _ [] = 0" |
"count x (y # xs) = (if x = y then 1 + (count x xs) else (count x xs))"

lemma [simp]: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = x # []" |
"snoc (y#ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x#xs) = snoc (reverse xs) x"

lemma [simp]: "reverse (snoc xs a) = a#(reverse xs)"
  apply(induction xs)
   apply(auto)
  done

lemma l4 [simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto n = n + (sum_upto (n-1))"

lemma l5: "sum_upto n = n * (n+1) div 2"
apply(induction n)
apply(auto)
done


datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l x r) = x#((contents l)@(contents r))"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l n r) = n + (sum_tree l) + (sum_tree r)"

lemma [simp]: "sum_tree t = sum_list (contents t)"
  apply(induction t)
  apply(auto)
  done

datatype 'a BinTree = Leaf 'a | Node "'a BinTree" 'a "'a BinTree"

fun mirror :: "'a BinTree \<Rightarrow> 'a BinTree" where
"mirror (Leaf x) = Leaf x" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

value "mirror (Node (Leaf 1) (2::nat) (Node (Leaf 4) 3 (Leaf 5)))"

lemma [simp]: "mirror (mirror t) = t"
  apply(induction t)
   apply(auto)
  done

fun pre_order :: "'a BinTree \<Rightarrow> 'a list" where
"pre_order (Leaf x) = [x]" |
"pre_order (Node l x r) = x#((pre_order l)@(pre_order r))"

value "pre_order (Node (Leaf 1) (2::nat) (Leaf 3))"

fun post_order :: "'a BinTree \<Rightarrow> 'a list" where
"post_order (Leaf x) = [x]" |
"post_order (Node l x r) = (post_order l)@(post_order r)@[x]"

value "post_order (Node (Leaf 1) (2::nat) (Leaf 3))"

lemma mirroring: "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a (x#y#xs) = x#a#(intersperse a (y#xs))" |
"intersperse _ xs = xs"

value "intersperse (1::nat) [2,2,2,2]"

lemma mapping: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
    apply(auto)
  done


fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

value "itadd 1 9"

lemma [simp]: "itadd m n = add m n"
  apply (induction m arbitrary: n)
   apply auto
  done

lemma simp_test: "(A \<and> B) = (if A then B else False)"
  apply(simp)
  done


declare [[names_short]]

datatype tree0 = Leaf | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf = 1" |
"nodes (Node l r) = 1 + (nodes l) + (nodes r)"

value "nodes (Node Leaf (Node (Node Leaf Leaf) Leaf))"
    
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

value "explode 2 leaf"

value "nodes (explode 6 Leaf)"  

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var n = n" |
"eval (Const k) _ = k" |
"eval (Add l r) n = (eval l n) + (eval r n)" |
"eval (Mult l r) n = (eval l n) * (eval r n)"

value "eval (Add (Mult (Const 2) Var) Var) 4"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] _ = 0" |
"evalp (a#bs) k = a + k*(evalp bs k)"

thm "evalp.simps"

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
  by auto

lemma  assumes T: "\<forall> x y. T x y \<or> T y x"
and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA "\<forall> x y. T x y \<longrightarrow> A x y"
and "A x y"
shows "T x y"
proof -
have ?thesis using A T assms(4) assms(5) by blast
  thus ?thesis by blast
qed

term "True \<longrightarrow> False"

lemma conj_rule: "\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> P \<and> (Q \<and> P)"
  apply(rule conjI)
   apply assumption 
  apply(rule conjI)
   apply(assumption)
  apply(assumption)
  done

lemma ex591: "\<exists>x. P \<and> Q(x) \<Longrightarrow> P \<and> (\<exists>x. Q(x))"
  apply(rule conjI)
  by auto


definition relA :: "(nat \<times> int) set" where
"relA = {(1,2), (2, 3)}"

definition relB :: "nat rel" where
"relB = {(3,4)}"

value "Image relA {1}"

value "(1::nat) # [2, 3] @ [4]"



(*typedecl state
consts M :: "(state \<times> state) set*)

end









