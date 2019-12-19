==================
Meta-Documentation
==================

How to build and publish this documentation?
============================================

Nothing really. Currently this documentation is hosted on https://cogent.readthedocs.io/.
Everything is carefully taken care of by `Read The Docs`_.
Just edit the source files and configuration files and everything should be automatic.

.. _Read The Docs: https://readthedocs.org/

How to build this documentation locally?
========================================

1. We use the Sphinx-rtd-theme from https://github.com/readthedocs/sphinx_rtd_theme.
   The theme files are not included in this repository, so if you want to build the
   html files, then follow the instructions here:
   https://sphinx-rtd-theme.readthedocs.io/en/latest/installing.html.
   Symblink or copy the directory ``sphinx_rtd_theme/sphinx_rtd_theme`` to ``docs-src/_themes/``.

2. Run ``make html`` or other target as desired.
