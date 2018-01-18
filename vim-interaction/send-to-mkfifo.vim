
"   The following script contains some simple functions
"   that allow a quite immersive experience using HOL Light.
"   We bind those functions to <F_> keys in order to allow
"   an immediate use of them and to typing each time a command.
"   
"   author: Massimo Nocentini
"
"

" UTILITY FUNCTIONS
" __________________________________________________________
  
" Quick and dirty approach to load `fifo_queue` var declaration
source ~/Developer/working-copies/logics/hol-light/mkfifo-sessions/current-session.vim

function! GetVisualSelection() range
    " Why is this not a built-in Vim script function?!
    let [lnum1, col1] = getpos("'<")[1:2]
    let [lnum2, col2] = getpos("'>")[1:2]
    let lines = getline(lnum1, lnum2)
    let lines[-1] = lines[-1][: col2 - (&selection == 'inclusive' ? 1 : 2)]
    "let lines[-1] = lines[-1][: col2 -1 ]
    let lines[0] = lines[0][col1 - 1:]
    return join(lines, "\n")
endfunction


" GENERAL EVALUATION
" __________________________________________________________

function! EvaluateVisualSelection() range
    let visual_selected_text = GetVisualSelection()
    let visual_selected_text = substitute(visual_selected_text, '`', '\\`', "g")
    "let visual_selected_text = substitute(visual_selected_text, '\(;;\)*\s*$', '', "g")
    "echom visual_selected_text
    echo system('echo "'.visual_selected_text.';;" > '.g:fifo_queue)
    let end_selection_position = line("'>")
    " echom "end line position:" . end_selection_position
    let pos = setpos(".", [0, end_selection_position + 1, 1, 0])
endfunction

" the following function look for an expression
" as a whole evaluating it, searching as terminating 
" string the token ";;"
function! SendExpressionToFifoDevice() range
    let start = line('.')
    " searching flags: 
    " `c` for accepting matching at cursor position
    " `s` to set a mark ' at the previous location
    let end = search(';;\s*$', 'cs') 
    echo system('sed -n '.start.','.end.'p '.expand('%').' > '.g:fifo_queue)
    let pos = setpos(".", [0, (end+1), 1, 0])
endfunction

function! EvaluateWordUnderCursor() range
    let word_under_cursor = expand("<cword>")
    " in the following we wrap the word under cursor in order
    " to handle possibly infix operator
    echo system('echo "let val_'.word_under_cursor.' = ('.word_under_cursor.');;" > '.g:fifo_queue)
endfunction

function! SendInterrupt()
    echo system(g:interrupt_command)
endfunction

function! SendDirectoryDirectiveCWD()
    echo system('echo "#directory \"'.getcwd().'\";;" > '.g:fifo_queue)
endfunction

" HOL Light dedicated interaction
" __________________________________________________


" The following function have the `range` attribute just
" to protect themself from been invoked during a selection
" that spans over multiple lines, in those cases each of
" the following functions should be called many times as
" the number of lines current selected, image the `undu`
" function been called several times!
function! UndoTacticApplication() range
    echo system('echo "b();;" > '.g:fifo_queue)
endfunction

function! AskHelpForObjectUnderCursor() range
    echo system('echo "help \"'.expand("<cword>").'\";;" > '.g:fifo_queue)
endfunction

function! PrintGoalStack() range
    echo system('echo "let val_goalstack_ = p ();;" > '.g:fifo_queue)
endfunction

function! EvaluateVisualSelectionAsGoal() range
    let visual_selected_text = GetVisualSelection()
    let visual_selected_text = substitute(visual_selected_text, '`', '\\`', "g")

    " it is interesting to observe that in the substitution we've to use escaping
    " on \ (ie, we write \\) inside '...' literal string construction, which means 
    " that string concat operator maybe handle string not in their literal form,
    " otherwise a simpler '\`' would have been sufficient.
    echo system('echo "g ('.visual_selected_text.');;" > '.g:fifo_queue)

    let end_selection_position = line("'>")
    " echom "end line position:" . end_selection_position
    let pos = setpos(".", [0, end_selection_position + 1, 1, 0])
endfunction

function! ApplyVisualSelectionAsTactic() range
    let visual_selected_text = GetVisualSelection()
    let visual_selected_text = substitute(visual_selected_text, '\s\s\+', " ", "g")
    let visual_selected_text = substitute(visual_selected_text, '`', '\\`', "g")
    let visual_selected_text = substitute(visual_selected_text, '^\s*THEN\s\+', "", "")
    let visual_selected_text = substitute(visual_selected_text, '\s\+THEN\s*$', "", "")
    " the following is an attempt to handle THENL directly
    "let visual_selected_text = substitute(visual_selected_text, '^\s*THENL\s*\[\(.*\)\]\s*$', "EVERY [\1])", "")
    "let visual_selected_text = substitute(visual_selected_text, '^\s*THENL\s*\[', 'EVERY [', "")
    " the following remove a trailing `;` when a line beloging to a list
    " is evaluated as a whole. Maybe it should be interesting to add
    " to the previous substitutions the handling of `THENL`, againg for tackling lists.
    let visual_selected_text = substitute(visual_selected_text, '\s*;\=\s*$', "", "")
    echo system('echo "e ('.visual_selected_text.');;" > '.g:fifo_queue)
    " the following is a simple attempt to place the cursor
    " after the last selected line but it doesn't work
    " let end_selection_position = getpos("'>")
    let end_selection_position = line("'>")
    " echom "end line position:" . end_selection_position
    " let pos = setpos(".", [0, end_selection_position + 1, 1, 0])
endfunction


" <F_> key bindings
" ________________________________________________________

:nmap <F2> :call AskHelpForObjectUnderCursor()<CR>
:nmap <F3> :call EvaluateWordUnderCursor()<CR>
:vmap <F4> :call EvaluateVisualSelection()<CR>
:nmap <F5> :call SendExpressionToFifoDevice()<CR>
:vmap <F6> :call EvaluateVisualSelectionAsGoal()<CR>
:vmap <F7> :call ApplyVisualSelectionAsTactic()<CR>
:nmap <F8> :call UndoTacticApplication()<CR>
:nmap <F9> :call PrintGoalStack()<CR>
:nmap <localleader>k :call SendInterrupt()<CR>
:nmap <localleader>cwd :call SendDirectoryDirectiveCWD()<CR>

