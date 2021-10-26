import lldb
import re

from typing import Pattern

regex_whitespace = re.compile(r"^\s*$")
regex_comment = re.compile(r"^[^\S\n]*(\/\/.*|\/\*(.|\n)*?\*\/)[^\S\n]*$")


def does_match(regex: Pattern, line: str):
    match = re.match(regex, line)
    return match is not None


def is_whitespace(line: str):
    return does_match(regex_whitespace, line)


def is_comment(line: str):
    return does_match(regex_comment, line)


def get_source_file(debugger: lldb.SBDebugger) -> str:
    target: lldb.SBTarget = debugger.GetSelectedTarget()
    module: lldb.SBModule = target.GetModuleAtIndex(0)
    unit: lldb.SBCompileUnit = module.GetCompileUnitAtIndex(0)
    file: lldb.SBFileSpec = unit.file

    return file.fullpath
