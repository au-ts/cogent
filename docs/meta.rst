==================
Meta-Documentation
==================

How to build this documentation?
================================

1. We use the Sphinx-rtd-theme from https://github.com/readthedocs/sphinx_rtd_theme.
   The theme files are not included in this repository, so if you want to build the
   html files, then follow the instructions here:
   https://sphinx-rtd-theme.readthedocs.io/en/latest/installing.html.
   Symblink or copy the directory ``sphinx_rtd_theme/sphinx_rtd_theme`` to ``docs-src/_themes/``.

2. Run ``make html`` or other target as desired.
