from typing import Dict, List, TypedDict, Union

BreakpointData = TypedDict(
    'BreakpointData', {'is_set': bool, 'variables': List[str]})

breakpoints: Dict[str, BreakpointData] = dict()

prefix = {"function":  "cogent/function/", "variable": "cogent/variable/"}
prefixes = tuple(prefix.values())


def register_breakpoint(function: str, variable: Union[str, None]):
    if not function in breakpoints:
        breakpoints[function] = BreakpointData(is_set=False, variables=[])

    if variable is not None:
        breakpoints[function]['variables'].append(variable)
    else:
        breakpoints[function]['is_set'] = True


def get_breakpoint_name(function: str, variable: Union[str, None]):
    if variable is None:
        return f"cogent/function/{function}"
    else:
        return f"cogent/variable/{function}/{variable}"


def split_breakpoint_name(name: str):
    if name.startswith(prefix["function"]):
        function = name.split("/")[-1]
        return (function, None)
    elif name.startswith(prefix["variable"]):
        [function, variable] = name.split("/")[-2:]
        return (function, variable)
    else:
        return (None, None)
