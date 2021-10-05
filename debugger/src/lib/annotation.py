import linecache
import lldb
import re
from typing import Literal, TypedDict, Union

from lib.util import does_match, is_comment, is_whitespace

VarAnnotation = TypedDict(
    'VarAnnotation', {'type': Literal['var'], 'value': str})

Annotation = Union[VarAnnotation]

regex_annotation_var = re.compile(r"^[^\S\n]*\/\* \$VAR: (\w+) \*\/[^\S\n]*$")


def is_var(annotation: str):
    return does_match(regex_annotation_var, annotation)


def extract_annotation(comment: str) -> Union[Annotation, None]:
    if is_var(comment):
        match = re.match(regex_annotation_var, comment)
        assert match is not None
        return {'type': 'var', 'value': match.group(1)}
    else:
        return None


def get_annotations(declaration: lldb.SBDeclaration):
    file_spec: lldb.SBFileSpec = declaration.GetFileSpec()
    filename: str = file_spec.GetFilename()
    line_num: int = declaration.GetLine()

    annotations = {}

    cur_line = line_num - 1
    while 0 <= cur_line:
        line = linecache.getline(filename, cur_line)
        if is_comment(line):
            annotation = extract_annotation(line)
            if annotation is not None:
                key = annotation["type"]
                val = annotation["value"]
                annotations[key] = val
        elif not is_whitespace(line):
            break

        cur_line -= 1

    return annotations
