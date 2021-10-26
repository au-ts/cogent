
import lldb

from argparse import _SubParsersAction, Namespace
from typing import Dict, List

import src.lib.color as color

import src.commands.breakpoint.shared as shared

from src.commands.breakpoint.shared import BreakpointData


def register_command(subparsers: _SubParsersAction):
    parser = subparsers.add_parser("list")
    parser.set_defaults(handler=list_breakpoints)


# TODO: use the target . GetBreakpoints... this will go stale
# def list_breakpoints(debugger: lldb.SBDebugger, args: Namespace, exe_ctx: lldb.SBExecutionContext, result: lldb.SBCommandReturnObject):
#     target: lldb.SBTarget = debugger.GetSelectedTarget()

#     if len(shared.breakpoints) == 0:
#         result.AppendMessage(
#             f"{color.BRIGHT_YELLOW}No breakpoints are set.{color.RESET}\n")
#         return

#     for function in shared.breakpoints:
#         is_set = shared.breakpoints[function]["is_set"]
#         result.AppendMessage(
#             f"\n{color.BRIGHT_BLUE}function {color.BRIGHT_MAGENTA if is_set else color.GREY}{function}{color.RESET}")

#         for variable in shared.breakpoints[function]["variables"]:
#             result.AppendMessage(
#                 f"  - {color.BRIGHT_BLUE}variable {color.BRIGHT_MAGENTA}{variable}{color.RESET}")

#     result.AppendMessage(" ")

def list_breakpoints(debugger: lldb.SBDebugger, args: Namespace, exe_ctx: lldb.SBExecutionContext, result: lldb.SBCommandReturnObject):
    target: lldb.SBTarget = debugger.GetSelectedTarget()

    breakpoints = get_breakpoints(target)
    breakpoint_data = process_breakpoints(breakpoints)

    if len(breakpoint_data) == 0:
        result.AppendMessage(
            f"{color.BRIGHT_YELLOW}No breakpoints are set.{color.RESET}\n")
        return

    for function in breakpoint_data:
        is_set = breakpoint_data[function]["is_set"]
        result.AppendMessage(
            f"\n{color.BRIGHT_BLUE}function {color.BRIGHT_MAGENTA if is_set else color.GREY}{function}{color.RESET}")

        for variable in breakpoint_data[function]["variables"]:
            result.AppendMessage(
                f"  - {color.BRIGHT_BLUE}variable {color.BRIGHT_MAGENTA}{variable}{color.RESET}")

    result.AppendMessage(" ")


def get_breakpoints(target: lldb.SBTarget) -> List[lldb.SBBreakpoint]:
    result: List[lldb.SBBreakpoint] = []
    for index in range(target.num_breakpoints):
        bkpt: lldb.SBBreakpoint = target.GetBreakpointAtIndex(index)
        names: List[str] = get_breakpoint_names(bkpt)
        if any(name.startswith(shared.prefixes) for name in names):
            result.append(bkpt)
    return result


def get_breakpoint_names(bkpt: lldb.SBBreakpoint) -> List[str]:
    str_list = lldb.SBStringList()
    bkpt.GetNames(str_list)

    result: List[str] = []
    for index in range(str_list.GetSize()):
        name: str = str_list.GetStringAtIndex(index)
        result.append(name)
    return result


def process_breakpoints(bkpt_list: List[lldb.SBBreakpoint]) -> Dict[str, BreakpointData]:
    result: Dict[str, BreakpointData] = dict()

    for bkpt in bkpt_list:
        names = get_breakpoint_names(bkpt)
        for name in names:
            (function, variable) = shared.split_breakpoint_name(name)
            if function is None:
                continue
            elif not function in result:
                result[function] = BreakpointData(
                    is_set=False, variables=[])

            if variable is None:
                result[function]['is_set'] = True
            else:
                result[function]['variables'].append(variable)
            break

    return result
