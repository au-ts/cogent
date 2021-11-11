# pour m'aider a rempalcer les chaines de caracteres dans les fichiers theory
import fileinput
import sys

folder =  sys.argv[1]
filename = f"{folder}/Generated_CorresSetup.thy"

utf8rep = {
   r"τ": r"\<tau>"
   , r"~": r"\<sim>"
   , r"∘": r"\<circ>"
   , r"λ": r"\<lambda>"
   , r"∃": r"\<exists>"
   , r"≡" :r"\<equiv>"
   , r"∧": r"\<and> "
 }

def makeRep(dic, ss):
    d = {}
    for s in ss:
      for i, j in dic.items():
          d[i + s] = j + s
    return d

# c'est pour les poly types
rep = dict({
    r"(* Put manual type and value relations below here *)":
r"""
(* Put manual type and value relations below here *)
instantiation U2_C :: cogent_C_val
begin
definition type_rel_U2_C_def:
  "type_rel typ (_ :: U2_C itself) ≡ typ = RCon ''U2'' []"
definition val_rel_U2_C_def:
  "val_rel uv (x :: U2_C) ≡ (∃size v. (uv = UAbstract (UUN size v )) ∧ size = 2 ∧ v = unat (U2_C.v_C x) ∧ U2_C.v_C x < 2 ^ size) "
instance ..
end
instantiation U4_C :: cogent_C_val
begin
definition type_rel_U4_C_def:
  "type_rel typ (_ :: U4_C itself) ≡ typ = RCon ''U4'' []"
definition val_rel_U4_C_def:
  "val_rel uv (x :: U4_C) ≡ (∃size v. (uv = UAbstract (UUN size v )) ∧ size = 4 ∧ v = unat (U4_C.v_C x) ∧ U4_C.v_C x < 2 ^ size) "
instance ..
end
"""

    , r'local_setup_val_rel_type_rel_put_them_in_buckets "main_pp_inferred.c" []': 
      r'local_setup_val_rel_type_rel_put_them_in_buckets "main_pp_inferred.c" [UAbstract "U2", UAbstract "U4"]'

    , r'local_setup_heap_rel "main_pp_inferred.c" [] []':
      r'local_setup_heap_rel "main_pp_inferred.c" ["U2_C", "U4_C"] [("32 word", "w32")]'

      , r'(* Put manual value relation definitions below here *)':
      r"""(* Put manual value relation definitions below here *)
  val_rel_U2_C_def
  val_rel_U4_C_def
  """

      , r'(* Put manual type relation definitions below here *)':
      r"""(* Put manual type relation definitions below here *)
  type_rel_U2_C_def
  type_rel_U4_C_def
  """
    })


def replace_all(text, dic):
    for i, j in dic.items():
        text = text.replace(i, j)
    return text

def replace_all_utf8(text, dic):
    for i, j in dic.items():
        text = text.replace(replace_all(i, utf8rep), replace_all(j, utf8rep))
    return text


with fileinput.FileInput(filename, inplace=True, backup='.bak') as file:
    for line in file:
        print(replace_all_utf8(line, rep), end='')
