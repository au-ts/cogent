import lldb

from os import path

debugger: lldb.SBDebugger = lldb.SBDebugger.Create()

# Load Cogent CLI
abspath = path.abspath(__file__)
dirname = path.dirname(abspath)
debugger.HandleCommand(f"command script import {dirname}")

# Start debug REPL
debugger.RunCommandInterpreter(
    True, False, lldb.SBCommandInterpreterRunOptions(), 0, False, False)
