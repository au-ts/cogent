-- |
-- Module      : Minigent.Syntax.PrettyPrint
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The ANSI colour scheme used by the pretty printer.
--
-- It expects to be imported qualified.
module Minigent.Syntax.PrettyPrint.Styles where

import Data.Text.Prettyprint.Doc.Render.Terminal

primType = color Blue

var = colorDull Yellow

func = colorDull Green

literal  = colorDull Green

constraintKeyword = color Magenta

sym = color Yellow

con = color Green

field = color Cyan

op = color Red

keyword = color Magenta

sigil = color Yellow

typeVar = colorDull Red

unifVar = colorDull Cyan

typeOp = colorDull Magenta

absType = color Black

