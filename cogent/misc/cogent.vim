"
" Copyright 2017, NICTA
"
" This software may be distributed and modified according to the terms of
" the GNU General Public License version 2. Note that NO WARRANTY is provided.
" See "LICENSE_GPLv2.txt" for details.
"
" @TAG(NICTA_GPL)
"

" Vim syntax file
" Language:		Cogent
" Maintainer:		Zilin Chen <z3350478@unsw.edu.au>
" Last Change:		10 Apr 2017
" Original Author:	Zilin Chen <z3350478@unsw.edu.au>
"
"

if exists("b:current_syntax")
  finish
endif
 
" Identifiers
syn match cogentTypeId "\<[A-Z][a-zA-Z0-9_']*"
syn match cogentVarDef "^[a-z_][a-zA-Z0-9_']*"
syn match cogentFieldId "\<[a-z][a-zA-Z0-9_']*" contained nextgroup=cogentFieldColon skipwhite
syn match cogentTag "[A-Z][a-zA-Z0-9_']*" contained nextgroup=cogentTypeId,cogentRecord,cogentVariant skipwhite

" Definitions
syn region cogentDefinition keepend start="^[a-z_][a-zA-Z0-9_']*\(.*=\|\s|\)"rs=s skip="\n\s" end="$" contains=cogentLetBang,cogentLineComment,cogentBlockComment,cogentBoolean,cogentSpecialChar,cogentCharacter,cogentString,cogentNumber,cogentOperator,cogentBar,cogentCaseArr,cogentSemiColon,cogentComma,cogentKeyword,cogentTypeId,cogentVarDef,cogentTakePut transparent
syn match cogentLetBang "!\s*[a-z_][a-zA-Z0-9_']*" containedin=cogentDefinition contained
syn region cogentTakePut start="{\|#{"rs=s end="}"re=e containedin=cogentDefinition contained contains=cogentLineComment,cogentBlockComment,cogentBoolean,cogentSpecialChar,cogentCharacter,cogentString,cogentNumber,cogentOperator,cogentBar,cogentCaseArr,cogentSemiColon,cogentComma,cogentKeyword,cogentTypeId,cogentTakePut,cogentOpenBrace,cogentCloseBrace,cogentLetBang transparent
syn match cogentOpenBrace "{\|#{" containedin=cogentTakePut contained
syn match cogentCloseBrace "}" containedin=cogenttakePut contained

" Typedef's
syn region cogentTypedef keepend matchgroup=Keyword start="^type\>" skip="\n\s" end="$" contains=cogentTypedefTypeId,cogentTypedefEq,cogentTypeType,cogentLineComment,cogentBlockComment transparent
" syn keyword cogentTypedefTypeKw type nextgroup=cogentTypedefTypeId skipwhite contained
syn match cogentTypedefTypeId "[A-Z][a-zA-Z0-9_']*" nextgroup=cogentTypedefEq skipwhite contained
syn match cogentTypedefEq "=" nextgroup=cogentTypeType skipwhite contained

" Type signatures
syn region cogentTypeSig keepend matchgroup=Identifier start="^[a-z_][a-zA-Z0-9_']*\s*\(:\)\@=" skip="\n\s" end="$" contains=cogentTypeSigColon,cogentTypeType,cogentLineComment,cogentBlockComment transparent
" syn match cogentTypeSigVarId "^[a-z][a-zA-Z0-9_']*" nextgroup=cogentTypeSigColon skipwhite contained
syn match cogentTypeSigColon ":" nextgroup=cogentTypeType skipwhite contained

syn region cogentTypeType start="." keepend skip="\n\s" end="$" contains=cogentKindSig,cogentTypeId,cogentRecord,cogentVariant,cogentAllT,cogentArrowT,cogentUnitT,cogentTakeT,cogentBangT,cogentUnboxT,cogentLineComment,cogentBlockComment transparent contained

syn region cogentKindSig matchgroup=PreProc start="\<all\>" keepend skip="\n\s" matchgroup=NONE end="\." contains=cogentInKind,cogentKinds,cogentLineComment,cogentBlockComment transparent contained


" Type constructors
syn region cogentRecord start="{" end="}" contains=cogentKindSig,cogentFieldId,cogentTypeId,cogentFieldColon,cogentRecord,cogentVariant,cogentUnitT,cogentArrowT,cogentBangT,cogentUnboxT,cogentTakeT,cogentLineComment,cogentBlockComment transparent contained
syn region cogentVariant start="<" end=">" contains=cogentVariantBar,cogentTag,cogentTypeId,cogentRecord,cogentVariant,cogentUnitT,cogentAllT,cogentArrowT,cogentBangT,cogentUnboxT,cogentTakeT,cogentLineComment,cogentBlockComment transparent contained
syn match cogentUnitT "()" contained
syn match cogentArrowT "->" contained
syn match cogentBangT "!" contained
syn match cogentUnboxT "#" contained
syn keyword cogentTakeT take put contained
syn match cogentInKind ":<" contained
syn match cogentKinds "[DES]" contained nextgroup=cogentComma,cogentCloseParens,cogentDot
syn match cogentVariantBar "|" contained

syn match cogentCloseParens ")"
syn match cogentDot "\."

syn match cogentFieldColon contained ":"

" " Constants
" syn match cogentBoolean "\<\(True\|False\)\>"
" syn match cogentSpecialChar "\\\([0-9]\+\|o[0-7]\+\|x[0-9a-fA-F]\+\|[\"\\'&\\abfnrtv]\|^[A-Z^_\[\\\]]\)"
" syn match cogentCharacter "[^a-zA-Z0-9_']'\([^\\]\|\\[^']\+\|\\'\)'"lc=1 contains=cogentSpecialChar
" syn match cogentCharacter "^'\([^\\]\|\\[^']\+\|\\'\)'" contains=cogentSpecialChar
" syn region cogentString start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=cogentSpecialChar
" syn match cogentNumber "\<[0-9]\+\>\|\<0[xX][0-9a-fA-F]\+\>\|\<0[oO][0-7]\+\>"

" Delimiter
syn match cogentBar "|"
syn match cogentCaseArr "\m\(->\|=>\|\~>\)"
syn match cogentSemiColon ";"
syn match cogentComma ","

" Operators
syn match cogentOperator "[+\-*/%><]\([^+\-*/%><]\|\n\)"he=s+1
syn match cogentOperator ">=\|<=\|==\|/=\|&&\|||\|\.&\.\|\.|\.\|\.\^\.\|>>\|<<"
syn keyword cogentOperator not complement

" Keywords
" syn keyword cogentType type
" syn keyword cogentInclude include
syn keyword cogentKeyword and in if then else let

" Comments
syn keyword cogentDev contained TODO FIXME XXX NOTE ASSERT containedin=cogentLineComment,cogentBlockComment

syn match   cogentLineComment      "--.*$" contains=cogentDev
syn region  cogentBlockComment     start="{-"  end="-}" contains=cogentBlockComment,cogentDev

" Include
syn match  cogentIncludeLine display "^include\>\s*["<]" contains=cogentIncludeStr
syn region cogentIncludeStr display start=+"+ skip=+\\\\\|\\+ end=+"+
syn match  cogentIncludeStr display contained "<[^>]*>" containedin=cogentIncludeLine


command -nargs=+ HiLink hi def link <args>

HiLink cogentType			    Keyword
HiLink cogentInclude			Keyword
HiLink cogentKeyword			Keyword
HiLink cogentDev				Todo

HiLink cogentTypdefTypeKw		Keyword
HiLink cogentTypdefTypeId		Type

HiLink cogentTypeSigVarId		Identifier

HiLink cogentTypeId             Type
HiLink cogentTakeT		        PreProc
HiLink cogentUnitT              PreProc
HiLink cogentArrowT		    	PreProc
HiLink cogentBangT              PreProc
HiLink cogentUnboxT		    	PreProc
HiLink cogentInKind		    	PreProc
HiLink cogentVariantBar	        PreProc

HiLink cogentKinds			    PreProc

HiLink cogentLetBang			PreProc

HiLink cogentOpenBrace		    Keyword
HiLink cogentCloseBrace     	Keyword

HiLink cogentVarDef		        Identifier

HiLink cogentBoolean			Boolean
HiLink cogentSpecialChar	    SpecialChar
HiLink cogentCharacter		    Character
HiLink cogentString			    String
HiLink cogentNumber			    Number

HiLink cogentOperator			Special

" HiLink cogentFieldId			Tag
HiLink cogentTag				Tag

HiLink cogentBlockComment		Comment
HiLink cogentLineComment        Comment

HiLink cogentIncludeStr         String
HiLink cogentIncludeLine        Keyword

delcommand HiLink


let b:current_syntax = "cogent"
