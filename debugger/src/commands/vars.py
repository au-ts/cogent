import lldb


import src.lib.annotation as annotation
import src.lib.color as color
from src. lib.annotation import LineAnnotationValue


def handler(debugger: lldb.SBDebugger, command: str, exe_ctx: lldb.SBExecutionContext, result: lldb.SBCommandReturnObject):
    frame: lldb.SBFrame = exe_ctx.GetFrame()

    variable_list: lldb.SBValueList = frame.GetVariables(
        True, True, True, True)
    variable_count: int = variable_list.GetSize()

    for i in range(variable_count):
        variable: lldb.SBValue = variable_list.GetValueAtIndex(i)
        declaration: lldb.SBDeclaration = variable.GetDeclaration()

        annotations = annotation.get_annotations(declaration)

        if 'var' in annotations:
            ty = variable.GetType()
            name = annotations['var']
            value = variable.GetValue() if is_initialized(
                frame, declaration) else f"{color.GREY}UNINITIALIZED{color.RESET}"

            result.AppendMessage(f"({ty}) {name} = {value}")

            if 'line' in annotations:
                data: LineAnnotationValue = annotations['line']
                file = data['file']
                line = data['line']
                col = data['col']

                result.AppendMessage(f"@{file}:{line}:{col}")


def is_initialized(frame: lldb.SBFrame, declaration: lldb.SBDeclaration) -> bool:
    """
    Checks if the variable declaration has been initialized or not.

    C variables will have junk data before initialization, but otherwise are not
    distinguishable.
    """

    line_entry: lldb.SBLineEntry = frame.GetLineEntry()

    cur_line: int = line_entry.GetLine()
    decl_line: int = declaration.GetLine()

    has_passed_line = decl_line < cur_line

    return has_passed_line
