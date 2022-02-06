from argparse import _SubParsersAction

import src.commands.breakpoint as breakpoint
import src.commands.step as step
import src.commands.vars as vars


def register_command(subparsers: _SubParsersAction):
    breakpoint.register_command(subparsers)
    step.register_command(subparsers)
    vars.register_command(subparsers)
