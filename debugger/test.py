import argparse
import shlex

parser = argparse.ArgumentParser(description="Cogent debugging facilities for LLDB")        
subparsers = parser.add_subparsers(dest="command")

def test():
  pass

# Variable mapping
parser_vars = subparsers.add_parser("vars")
parser_vars.set_defaults(handler=test)

while True:
  command = input("Enter: ")
  command_args = shlex.split(command)

  print(f"command_args = {command_args}")
  result = parser.parse_args(command_args)
  print(f"result = {result}")