" Vim syntax file
" Language:     Zélus
" Maintainers:  Virgile Andreani    <virgile.andreani@ens.fr>
" Filenames:    *.zls

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
    syntax clear
elseif exists("b:current_syntax") && b:current_syntax == "zelus"
    finish
endif

" Zélus is case sensitive
syn case match

" Comments
syn region Comment start="(\*" end="\*)" contains=Comment

" Strings
syn region String start=+"+ skip=+\\\\\|\\"+ end=+"+

" Booleans
syn keyword Boolean true false

" Identifiers
syn match Identifier /\a\('\?\w\)*/

" Constructors
syn match Typedef /\u\('\?\w\)*/

" Numbers
syn match Number /\d\d*/
syn match Number /0[xX]\x\x*/
syn match Number /0[oO]\o\o*/
syn match Number /0[bB][01][01]*/

" Characters
syn match Character /'\\\d\d\d'/
syn match Character /'\\[\'ntbr]'/
syn match Character /'.'/

" Floats
syn match Float /-\?\d\d*\(\.\d*\)\?\([eE][+-]\?\d\d*\)\?/

" Keywords
syn keyword Include open
syn keyword Statement reset every disc unsafe type quo
syn keyword Conditional if then else until unless match with end pre fby next up init last
syn keyword Repeat do done continue
syn keyword Label node automaton hybrid discrete
syn keyword Operator "land" "lor" "lxor" "lsl" "lsr" "asr" "mod"
syn keyword Keyword atomic der and or fun let in val rec inline local where as on
syn keyword Exception emit present period

" Todo
syn keyword Todo TODO FIXME XXX

let b:current_syntax = "zelus"

