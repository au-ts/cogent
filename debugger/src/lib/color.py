import os
import platform

if platform.system == "Windows":
    # Should let the colours work on Windows
    os.system("color")

BRIGHT_BLUE = "\u001b[34;1m"
BRIGHT_GREEN = "\u001b[32;1m"
BRIGHT_MAGENTA = "\u001b[35;1m"
BRIGHT_RED = "\u001b[31;1m"
BRIGHT_YELLOW = "\u001b[33;1m"
GREY = "\u001b[30;1m"
RESET = "\u001b[0m"
