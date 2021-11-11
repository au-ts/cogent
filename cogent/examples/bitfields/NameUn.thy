theory NameUn
  imports 
  
"HOL-Library.Char_ord"
begin    


fun string_of_nat :: "nat \<Rightarrow> string"
where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)] else 
     string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"
declare string_of_nat.simps [simp del]

lemma string_of_nat_lt10[simp] : "n < 10 \<Longrightarrow> string_of_nat n =
[char_of (48 + n)]"
  using  string_of_nat.simps
  by metis

lemma string_of_nat_ge10[simp] : "n \<ge> 10 \<Longrightarrow> string_of_nat n =
string_of_nat (n div 10) @ [char_of (48 + (n mod 10))]"
  using  string_of_nat.simps
  by (meson leD)

lemma string_of_nat_10_div:
  fixes n :: nat
  shows \<open>(\<And>k m. m < 10 \<Longrightarrow> P (10 * k + m)) \<Longrightarrow> P n\<close>
  by (metis mod_less_divisor mult_div_mod_eq zero_less_numeral)



lemma string_of_nat_never_nil: \<open>string_of_nat n \<noteq> []\<close>
  apply (induct n rule: string_of_nat_10_div)
  apply (case_tac \<open>10 * k + m < 10\<close>; force)
  done


lemma string_of_nat_split10:
  assumes
    \<open>n < 10\<close>
    \<open>0 < m\<close>
  shows
    \<open>string_of_nat (10 * m + n) = string_of_nat m @ string_of_nat n\<close>
  using assms
  by clarsimp

lemma string_of_nat_ind : "(\<And>n. n \<ge> 10 \<Longrightarrow> P (n div 10) \<Longrightarrow> P n) \<Longrightarrow>
(\<And> n. n < 10 \<Longrightarrow> P n) \<Longrightarrow> P (n :: nat)"
  apply (induct n rule:string_of_nat.induct)
  apply (cases "n \<ge> 10")
  using leI apply blast
  using leI apply blast
  done

lemma string_of_nat_ind' : "(\<And>k n. k > 0 \<Longrightarrow> n < 10 \<Longrightarrow> P k \<Longrightarrow> P (10 * k + n)) \<Longrightarrow>
(\<And> n. n < 10 \<Longrightarrow> P n) \<Longrightarrow> P (n :: nat)"
  apply (rule string_of_nat_ind)
   apply(induct n rule:string_of_nat_10_div)
   apply simp
  apply (metis div_greater_zero_iff mod_less_divisor mult_div_mod_eq zero_less_numeral)
  
  apply simp
  done

  

lemma string_of_nat_inj': " string_of_nat n = string_of_nat m \<longrightarrow> n = m"
  apply (induct n arbitrary: m rule:string_of_nat_ind' )
   apply simp
   apply(rename_tac k n m')
   apply (induct_tac m' rule: string_of_nat_10_div)
  apply(intro impI)
   apply simp
   apply (case_tac ka)
    apply (simp add:string_of_nat_never_nil)
   apply simp
  apply (induct_tac m rule: string_of_nat_10_div)
  apply(intro impI)
  apply simp
  apply(case_tac k)
   apply simp
  apply simp
  using string_of_nat_never_nil
  by metis

lemma string_of_nat_inj: " string_of_nat n = string_of_nat m \<Longrightarrow> n = m"
  using string_of_nat_inj'
  by blast



lemma string_of_nat_at0_le : 
"string_of_nat n ! 0 \<le> CHR 57"
  apply(simp add:less_eq_char_def)

  apply(induct_tac n rule: string_of_nat_ind')
   apply simp
  using string_of_nat_never_nil
   apply (metis append_Cons list.exhaust nth_Cons_0)
  apply simp
  done

fun name_un :: "nat \<Rightarrow> string"
where "name_un n = ''U'' @ string_of_nat n"




end