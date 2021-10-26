import lldb

from argparse import _SubParsersAction

import src.lib.util as util


def register_command(subparsers: _SubParsersAction):
    parser = subparsers.add_parser("step")
    parser.set_defaults(handler=handler)


def handler(debugger: lldb.SBDebugger, command: str, exe_ctx: lldb.SBExecutionContext, result: lldb.SBCommandReturnObject):
    target: lldb.SBTarget = debugger.GetSelectedTarget()

    filepath = util.get_source_file(debugger)
    file_spec = lldb.SBFileSpec(filepath)

    bkpt: lldb.SBBreakpoint = target.BreakpointCreateBySourceRegex(
        r"\$VAR:", file_spec)
    debugger.HandleCommand("continue")
    target.BreakpointDelete(bkpt.id)
