# pour m'aider a rempalcer les chaines de caracteres dans les fichiers theory
import fileinput
import sys
import re

cfilename = 'generated.c'
hfilename = 'generated.h'


def replace_all(text, dic):
    for i, j in dic.items():
        text = text.replace(i, j)
    return text



# finds a line "typedef t3 $easyName;", and returns t3 in this case
def find_C_name(easyName):
    with fileinput.FileInput(cfilename) as cfile:
      for line in cfile:
        search = re.search(r"^typedef (\w*) " + easyName + r";$", line)
        if search:
            return search.group(1)
    return False

Centry = find_C_name("Entry")

if not Centry:
    print("Not found: Name of the C Entry struct")
    exit(1)

Cstuff = find_C_name("Stuff")

if not Cstuff:
    print("Not found: Name of the C Stuff struct")
    exit(1)


# This function replaces in the C file:
#
# struct $structname {
#    ...
#  };
#
# with $repl
def replace_struct(structname, repl):
    # standard output is redirected to the file
    with fileinput.FileInput(cfilename, inplace=True) as cfile:
      foundIt = False
      finished = False
      for line in cfile:
          if finished:
              # write back the same line without any change
              print(line, end='')
          elif foundIt:
              if line.replace(" ", "") == "};\n":
                  print(repl)
                  print("// finished")
                  finished = True
          elif line.replace(" ", "") == "struct" + structname + "{\n":
                print("// found it")
                foundIt = True
          else:
              print(line, end='')

# move the Stuff struct before the definition of the C entry struct
# by first removing it, and then adding it
replace_struct(Cstuff, "")
wantedEntryStuff = "struct %s { int id; %s stuff; int value;} ;" % (Centry, Cstuff)
print("Replacing the generated C Entry struct with " + wantedEntryStuff)
replace_struct(Centry, (("struct %s { u32 a; u32 b ; u32 c ; } ;\n" % Cstuff) + wantedEntryStuff  ))

# This function replaces in the C file:
#
# static .. $funname(..)
#    ...
#  }
#
# with 
#
# static .. $funname$repl
#
# Note: $funname can be a regexp
def replace_fun(funname, repl):
    with fileinput.FileInput(cfilename, inplace=True) as cfile:
      foundIt = False
      for line in cfile:
          if foundIt:
              if line.replace(" ", "") == "}\n":
                  foundIt = False
          else:
            search = re.search(r"^(static.*" + funname + r")\(.*\)$", line)
            if search:
                print(search.group(1) + repl)
                foundIt = True
            else:
                print(line, end='')



replace_fun("get_id", "(%s *b) { return b->id ; }" % Centry)
replace_fun("set_id", "(%s *b, u32 v) { b->id = v ; }" % Centry)
replace_fun("get_value", "(%s *b) { return b->value ; }" % Centry)
replace_fun("set_value", "(%s *b, u32 v) { b->value = v ; }" % Centry)
replace_fun(r"part\d+", "() { }")

# Remove the (redundant) definition of CEntry
with fileinput.FileInput(cfilename, inplace=True) as cfile:
      for line in cfile:
          if line == "typedef struct { int id; Stuff stuff; int value; } CEntry;\n":
              print("typedef Entry CEntry;")
          else:
              print(line, end='')
