import fileinput
import sys
import re
import os



#if len(sys.argv) != 3:
#    print("Usage: make branch filename (without .cogent) ")
#    exit(0)

#branch = sys.argv[1]
#name   = sys.argv[2]
#os.system("bash ../compile-gen-getset.sh %s %s" %(branch, name))
        # pour m'aider a rempalcer les chaines de caracteres dans les fichiers theory


name="main_pp_inferred"
folder =  sys.argv[1]
cfilename = "%s/%s.c" % (folder, name)


def prepend_to_file(filename, text):
    f = open(filename,'r')
    temp = f.read()
    f.close()
    f = open(filename, 'w')
    f.write(text)
    f.write(temp)
    f.close()

# This function replaces in the C file:
#
# static .. $funname(t1)
#    t2
#  }
#
# with 
#
# static .. $funname$repl(t1,t2)
#
# Note: $funname can be a regexp
def replace_fun(funname, repl):
    with fileinput.FileInput(cfilename, inplace=True) as cfile:
      foundIt = False
      t0 = ""
      t1 = ""
      t2 = ""
      for line in cfile:
          if foundIt:
              if line.replace(" ", "") == "}\n":
                  foundIt = False
                  print(t0 + repl(t1,t2 + "}\n"))
                  t0 = ""
                  t1 = ""
                  t2 = ""
              else:
                  t2 += line
          else:
            search = re.search(r"^(static.*" + funname + r")\((.*)\)$", line)
            if search:
                t0 = search.group(1)
                t1 = search.group(2)
                t2 = ""
                foundIt = True
            else:
                print(line, end='')

def make_un(u_name, f_name):
    def replace_geta(decl, body):
        body_rep = re.sub(rf"return \(({u_name})\)(.*);", r"return (\1)  { \2 };", body)
        return "(%s) \n %s" % (decl, body_rep)
    def replace_seta(decl, body):
        body_rep = re.sub(r" v ", r" v.v", body)
        return "(%s) \n %s" % (decl, body_rep)
        
    #prepend_to_file(cfilename, "typedef struct U7 { char val; } U7;\n")
    replace_fun(fr"get_{f_name}", replace_geta)
    replace_fun(fr"set_{f_name}", replace_seta)


make_un("U2", "f2")
make_un("U4", "f3")

