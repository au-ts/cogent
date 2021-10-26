from argparse import _SubParsersAction, Namespace, OPTIONAL
import linecache
import re
from typing import List
import lldb

import src.lib.color as color
import src.lib.util as util

import src.commands.breakpoint.shared as shared


def register_command(subparsers: _SubParsersAction):
    parser = subparsers.add_parser("add")
    parser.set_defaults(handler=add)
    parser.add_argument("function")
    parser.add_argument("variable", nargs=OPTIONAL)


def find_decl_line(filepath: str, lineno: int):
    for offset, line in enumerate(linecache.getlines(filepath)[lineno - 1:]):
        if not (util.is_comment(line) or util.is_whitespace(line)):
            return lineno + offset


def add(debugger: lldb.SBDebugger, args: Namespace, exe_ctx: lldb.SBExecutionContext, result: lldb.SBCommandReturnObject):
    target: lldb.SBTarget = debugger.GetSelectedTarget()
    function: str = args.function
    variable: str = args.variable

    if variable is None:
        bkpt: lldb.SBBreakpoint = target.BreakpointCreateByName(
            function, target.executable.fullpath)

        if bkpt.GetNumLocations() == 0:
            result.AppendMessage(
                f"{color.BRIGHT_RED}Could not resolve function {function}.{color.RESET}")
            return

        result.AppendMessage(
            f"{color.BRIGHT_GREEN}Breakpoint set on function {function}.{color.RESET}")
        bkpt.AddName(f"cogent/function/{function}")

        shared.register_breakpoint(function, variable=None)
    else:
        symbols: lldb.SBSymbolContextList = target.FindFunctions(function)
        functions: List[lldb.SBFunction] = symbols.get_function_array()

        filepath = util.get_source_file(debugger)

        for fn in functions:
            addr: lldb.SBAddress = fn.addr
            line_entry: lldb.SBLineEntry = addr.line_entry
            assert(line_entry is not None)

            start: int = line_entry.line - 1
            for offset, line in enumerate(linecache.getlines(filepath)[start:]):
                lineno = offset + line_entry.line

                if re.match(r"^}\s*$", line):
                    # Only look inside the function's block
                    result.AppendMessage(
                        f"{color.BRIGHT_RED}Could not find variable named {variable} in function {function}. {color.RESET}")
                    break

                if line.strip() == f"/* $VAR:{variable} */":
                    decl_line = find_decl_line(filepath, lineno)
                    bkpt: lldb.SBBreakpoint = target.BreakpointCreateByLocation(
                        filepath, decl_line)
                    result.AppendMessage(
                        f"{color.BRIGHT_GREEN}Breakpoint set on variable {variable} in function {function}.{color.RESET}")

                    bkpt.AddName(f"cogent/variable/{function}/{variable}")

                    shared.register_breakpoint(function, variable)
                    break
