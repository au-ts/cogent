from argparse import _SubParsersAction

import src.commands.breakpoint.add as add
import src.commands.breakpoint.delete as delete
import src.commands.breakpoint.list as list

__all__ = ["add", "delete", "list"]


def register_command(subparsers: _SubParsersAction):
    parser_breakpoint = subparsers.add_parser(
        "breakpoint", aliases=['break', 'b'])
    subparsers_breakpoint = parser_breakpoint.add_subparsers()

    add.register_command(subparsers_breakpoint)
    delete.register_command(subparsers_breakpoint)
    list.register_command(subparsers_breakpoint)
