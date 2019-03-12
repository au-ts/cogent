theory proofs
  imports
    "autocorres-1.4/autocorres/AutoCorres"
begin

(* To run this file you need the AutoCorres tool used
   in the lecture.

  1. Download AutoCorres from 
       \url{http://www.cse.unsw.edu.au/~cs4161/autocorres-1.4.tar.gz}

  2. Unpack the .tar.gz file, which will create the directory autocorres-1.4
       tar -xzf autocorres-1.4.tar.gz

  3. Build the AutoCorres heap
     L4V_ARCH=X64 isabelle build -v -b -d autocorres-1.4 AutoCorres

  4. Load this file using the AutoCorres heap
     L4V_ARCH=X64 isabelle jedit -d autocorres-1.4 -l AutoCorres exam.thy

*)

(***********************************)
(* QUESTION 4: C code verification *)
(***********************************)
install_C_file "generated.c"
autocorres  "generated.c" (*[unsigned_word_abs = d5_get_a_tag_part0 d30_set_a_tag_part0]*)
context generated begin


thm d5_get_a_tag_part0'_def
thm d30_set_a_tag_part0'_def

thm "is_valid_w32_def"
term "is_valid_w32"
term "the"
term "heap_w32"

find_theorems "_ && _"
thm "word_of_int_def"
thm "max_word_def"

thm is_valid_w32_def
lemma mask:
  "(0xFFFFFFFF :: 32 word) = max_word"
  apply (unfold max_word_def)
  apply clarsimp
  done


lemma a_tag_part0_get_set_inverses[wp]:
   "\<lbrace>\<lambda>s. True \<rbrace>
      d30_set_a_tag_part0' b v
    \<lbrace>\<lambda>r s. d5_get_a_tag_part0' b s \<noteq> None \<longrightarrow> the (d5_get_a_tag_part0' b s) = v \<rbrace>"
  apply (unfold d30_set_a_tag_part0'_def d5_get_a_tag_part0'_def)
  apply wp
  using [[show_types]]
  apply (clarsimp simp add: oguard_def ogets_def obind_def mask fun_upd_same split: if_splits)
  done

lemma a_tag_part0_get_set_inverses'[wp]:
   "\<lbrace>\<lambda>s. True \<rbrace>
      d30_set_a_tag_part0' b v
    \<lbrace>\<lambda>r s. d5_get_a_tag_part0' b s  = Some v \<rbrace>"
  apply (unfold d30_set_a_tag_part0'_def d5_get_a_tag_part0'_def)
  apply wp
  using [[show_types]]
  apply (clarsimp simp add: oguard_def ogets_def obind_def mask fun_upd_same split: if_splits)
  done

thm d4_get_a_tag'_def
thm d29_set_a_tag'_def

lemma a_tag_get_set_inverses:
   "\<lbrace>\<lambda>s. True \<rbrace>
      d29_set_a_tag' b v
    \<lbrace>\<lambda>r s. d4_get_a_tag' b s = Some v \<rbrace>"
  apply (unfold d4_get_a_tag'_def d29_set_a_tag'_def)
  apply (clarsimp simp add: mask)
  apply wp
  done


thm d7_get_a_A_part0'_def
thm d32_set_a_A_part0'_def

lemma a_A_part0_get_set_inverses[wp]:
   "\<lbrace>\<lambda>s. True \<rbrace>
      d32_set_a_A_part0' b v
    \<lbrace>\<lambda>r s. d7_get_a_A_part0' b s = Some (v && 0xFF) \<rbrace>"
  apply (unfold d7_get_a_A_part0'_def d32_set_a_A_part0'_def)
  apply wp
  apply (clarsimp simp add: oguard_def ogets_def obind_def fun_upd_same split: if_splits)
  sorry


thm d6_get_a_A'_def
thm d31_set_a_A'_def

lemma a_A_get_set_inverses[wp]:
   "\<lbrace>\<lambda>s. True \<rbrace>
      d31_set_a_A' b v
    \<lbrace>\<lambda>r s. d6_get_a_A' b s = Some (v && 0xFF) \<rbrace>"
  apply (unfold d6_get_a_A'_def d31_set_a_A'_def)
  (* The value 2^31 doesn't make sense in the guard because we aren't dealing with signed ints!*)
  apply (clarsimp simp add: oguard_def ogets_def obind_def split: if_splits option.splits)
  apply wp
  sorry


thm d3_get_a'_def
thm d28_set_a'_def

thm "TAG_ENUM_A_def"

  
end
  
end
