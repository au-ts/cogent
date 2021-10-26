#!/usr/bin/env python

# <https://lldb.llvm.org/use/python-reference.html#create-a-new-lldb-command-using-a-python-function>
# <https://github.com/llvm/llvm-project/blob/main/lldb/examples/python/cmdtemplate.py>

import argparse
import inspect
import lldb
import shlex
import sys

from ast import parse
from typing import Any, Mapping, Optional

import src.commands.breakpoint
import src.commands.step
import src.commands.vars


class CogentCLI:
    program = 'cogent'

    @classmethod
    def register_lldb_command(cls, debugger, module_name):
        parser = cls.create_options()
        cls.__doc__ = parser.format_help()
        # Add any commands contained in this module to LLDB
        command = 'command script add -c %s.%s %s' % (module_name,
                                                      cls.__name__,
                                                      cls.program)
        debugger.HandleCommand(command)
        print(f"module_name = {module_name}.{cls.__name__}")
        print('The "{0}" command has been installed, type "help {0}" or "{0} '
              '--help" for detailed help.'.format(cls.program))

    @classmethod
    def create_options(cls):
        parser = argparse.ArgumentParser(
            description="Cogent debugging facilities for LLDB")
        subparsers = parser.add_subparsers()

        # Variable mapping
        parser_vars = subparsers.add_parser("vars")
        parser_vars.set_defaults(handler=src.commands.vars.handler)

        # Breakpoint
        src.commands.breakpoint.register_command(subparsers)

        # Stepping
        src.commands.step.register_command(subparsers)

        return parser

    def parse_options(self, command: str) -> Optional[argparse.Namespace]:
        # Use the Shell Lexer to properly parse up command options just like a
        # shell would
        command_args = shlex.split(command)

        try:
            return self.parser.parse_args(command_args)
        except SystemExit:
            # if you don't handle exceptions, passing an incorrect argument to
            # the OptionParser will cause LLDB to exit (courtesy of OptParse
            # dealing with argument errors by throwing SystemExit)
            return None

    def get_short_help(self):
        return "Cogent debugging utilities.\n"

    def get_long_help(self):
        return self.help_string

    def __init__(self, debugger: lldb.SBDebugger, internal_dict: Mapping[str, Any]):
        self.parser = self.create_options()
        self.help_string = self.parser.format_help()

    def __call__(self, debugger: lldb.SBDebugger, command: str, exe_ctx: lldb.SBExecutionContext, result):
        parsed_args = self.parse_options(command)

        if parsed_args is None:
            return

        if callable(getattr(parsed_args, 'handler', None)):
            parsed_args.handler(debugger, parsed_args, exe_ctx, result)
        else:
            debugger.HandleCommand('help cogent')


def __lldb_init_module(debugger: lldb.SBDebugger, internal_dict: Mapping[str, Any]):
    # Register all classes that have a register_lldb_command method
    for _name, cls in inspect.getmembers(sys.modules[__name__]):
        if inspect.isclass(cls) and callable(getattr(cls,
                                                     "register_lldb_command",
                                                     None)):
            cls.register_lldb_command(debugger, __name__)
