import linecache
import lldb
import re
from typing import Literal, TypedDict, Union

from src.lib.util import does_match, is_comment, is_whitespace

VarAnnotation = TypedDict(
    'VarAnnotation', {'type': Literal['var'], 'value': str})

LineAnnotationValue = TypedDict(
    'LineAnnotationValue', {'file': str, 'line': int, 'col': int})
LineAnnotation = TypedDict(
    'LineAnnotation', {'type': Literal['line'], 'value': LineAnnotationValue}
)

Annotation = Union[VarAnnotation, LineAnnotation]

regex_annotation_var = re.compile(
    r"^[^\S\n]*\/\* \$VAR:\s*(\w+) \*\/[^\S\n]*$")
regex_annotation_line = re.compile(
    r"^[^\S\n]*\/\* \$LINE: \"([^\"]+)\" : (\d+) : (\d+) \*\/[^\S\n]*$")


def is_var(annotation: str):
    return does_match(regex_annotation_var, annotation)


def is_line(annotation: str):
    return does_match(regex_annotation_line, annotation)


def extract_annotation(comment: str) -> Union[Annotation, None]:
    if is_var(comment):
        match = re.match(regex_annotation_var, comment)
        assert match is not None
        return {'type': 'var', 'value': match.group(1)}
    elif is_line(comment):
        match = re.match(regex_annotation_line, comment)
        assert match is not None
        return {'type': 'line', 'value': {
            'file': match.group(1),
            'line': int(match.group(2)),
            'col': int(match.group(3))
        }}
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
