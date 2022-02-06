import lldb

from argparse import _SubParsersAction

import src.lib.annotation as annotation
import src.lib.color as color

from src.lib.annotation import LineAnnotationValue


def register_command(subparsers: _SubParsersAction):
    parser = subparsers.add_parser("vars")
    parser.set_defaults(handler=handler)


def handler(
    debugger: lldb.SBDebugger,
    command: str,
    exe_ctx: lldb.SBExecutionContext,
    result: lldb.SBCommandReturnObject,
):
    frame: lldb.SBFrame = exe_ctx.GetFrame()

    variable_list: lldb.SBValueList = frame.GetVariables(True, True, True, True)
    variable_count: int = variable_list.GetSize()

    for i in range(variable_count):
        variable: lldb.SBValue = variable_list.GetValueAtIndex(i)
        declaration: lldb.SBDeclaration = variable.GetDeclaration()

        annotations = annotation.get_annotations(declaration)

        if "var" in annotations:
            name: str = annotations["var"]

            if name.startswith("x__"):
                continue

            value = get_value(variable, name)
            result.AppendMessage(value)

            if "line" in annotations:
                data: LineAnnotationValue = annotations["line"]
                file = data["file"]
                line = data["line"]
                col = data["col"]

                # result.AppendMessage(f"@{file}:{line}:{col}")


def get_value(variable: lldb.SBValue, name: str) -> str:
    if is_initialized(variable):
        if variable.TypeIsPointerType():
            value: lldb.SBValue = variable.Dereference()
            desc = lldb.SBStream()
            value.GetDescription(desc)

            data: str = desc.GetData()

            return data.replace(f"{variable.GetName()} =", f"{name} =")
        else:
            ty = variable.GetType()
            value = variable.GetValue()
            return f"({ty}) {name} = {value}"
    else:
        return f"{name} = {color.GREY}UNINITIALIZED{color.RESET}"


def is_initialized(variable: lldb.SBValue) -> bool:
    """
    Checks if the variable declaration has been initialized or not.

    C variables will have junk data before initialization, but otherwise are not
    distinguishable.
    """

    frame: lldb.SBFrame = variable.GetFrame()
    declaration: lldb.SBDeclaration = variable.GetDeclaration()

    line_entry: lldb.SBLineEntry = frame.GetLineEntry()

    cur_line: int = line_entry.GetLine()
    decl_line: int = declaration.GetLine()

    has_passed_line = decl_line < cur_line

    return has_passed_line
