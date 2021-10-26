
from typing import List, Union
import lldb

from argparse import OPTIONAL, _SubParsersAction, Namespace

import src.lib.color as color

import src.commands.breakpoint.shared as shared


def register_command(subparsers: _SubParsersAction):
    parser = subparsers.add_parser("delete")
    parser.set_defaults(handler=delete_breakpoint)

    parser.add_argument("function")
    parser.add_argument("variable", nargs=OPTIONAL)


def delete_breakpoint(debugger: lldb.SBDebugger, args: Namespace, exe_ctx: lldb.SBExecutionContext, result: lldb.SBCommandReturnObject):
    target: lldb.SBTarget = debugger.GetSelectedTarget()

    function: str = args.function
    variable: Union[str, None] = args.variable

    bkpt_list = find_breakpoints(
        target, shared.get_breakpoint_name(function, variable))

    if len(bkpt_list) == 0:
        result.AppendMessage(
            f"{color.BRIGHT_YELLOW}No matching breakpoints.{color.RESET}")
        return

    num_deleted = 0
    for bkpt in bkpt_list:
        was_success = target.BreakpointDelete(bkpt.id)
        num_deleted = num_deleted + (1 if was_success else 0)

    result.AppendMessage(
        f"{color.BRIGHT_GREEN}{num_deleted} breakpoint(s) deleted.{color.RESET}")


def find_breakpoints(target: lldb.SBTarget, name: str) -> List[lldb.SBBreakpoint]:
    bkpt_list = lldb.SBBreakpointList(target)
    target.FindBreakpointsByName(name, bkpt_list)

    result: List[lldb.SBBreakpoint] = []
    for index in range(bkpt_list.GetSize()):
        result.append(bkpt_list.GetBreakpointAtIndex(index))
    return result
