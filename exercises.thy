theory exercises
  imports Main
begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0" |
  "count x (t # L) = (if x = t then Suc (count x L) else count x L)"

lemma "count x xs \<le> length xs"
  apply (induction xs)
   apply auto
  done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] t = [t]" | 
"snoc (x # xs) t = x # (snoc xs t)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"



lemma "reverse (reverse xs) = xs"
  apply (induction xs)
  apply auto


end