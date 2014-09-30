function Test() 
    let start = line('.')
    let end = search("^$") - 1
    echo system('echo '.join(getline(start, end)).' > /tmp/hol_light')
endfunction

"dump selected lines
function! DumpLinesFirst() range
  echo system('sed -n '.a:firstline.','.a:lastline.'p '.expand('%').' > /tmp/hol_light')
  endfunction  
  
function! SendExpressionToFifoDevice() range
    let start = line('.')
    let end = search(';;\s*$') 
    echo system('sed -n '.start.','.end.'p '.expand('%').' > /tmp/hol_light')
    let pos = setpos(".", [0, (end+1), 1, 0])
endfunction

function! UndoTacticApplication() range
    echo system('echo "b();;" > /tmp/hol_light')
endfunction

function! AskHelpForObjectUnderCursor() range
    echo system('echo "help \"'.expand("<cword>").'\";;" > /tmp/hol_light')
endfunction

function! EvaluateWordUnderCursor() range
    let word_under_cursor = expand("<cword>")
    echo system('echo "let val_'.word_under_cursor.' = '.word_under_cursor.';;" > /tmp/hol_light')
endfunction

" This function isn't used up to now but deserve some study 
function! s:get_visual_selection()
    " Why is this not a built-in Vim script function?!
    let [lnum1, col1] = getpos("'<")[1:2]
    let [lnum2, col2] = getpos("'>")[1:2]
    let lines = getline(lnum1, lnum2)
    let lines[-1] = lines[-1][: col2 - (&selection == 'inclusive' ? 1 : 2)]
    let lines[0] = lines[0][col1 - 1:]
    return join(lines, "\n")
endfunction

function! EvaluateVisualSelection() 
    let visual_selected_text = getline("'<")[getpos("'<")[2]-1:getpos("'>")[2]-1]
    let visual_selected_text = substitute(visual_selected_text, '`', '\\`', "g")
    echo system('echo "let val_visual_selection = '.visual_selected_text.';;" > /tmp/hol_light')
endfunction

function! EvaluateVisualSelectionAsGoal() 
    let visual_selected_text = getline("'<")[getpos("'<")[2]-1:getpos("'>")[2]-1]
    let visual_selected_text = substitute(visual_selected_text, '`', '\\`', "g")
    " echo visual_selected_text

    " it is interesting to observe that in the substitution we've to use escaping
    " on \ (ie, we write \\) inside '...' literal string construction, which means 
    " that string concat operator maybe handle string not in their literal form,
    " otherwise a simpler '\`' would have been sufficient.
    echo system('echo "g ('.visual_selected_text.');;" > /tmp/hol_light')

    " the following is the former version that assumed to consume a naked term, 
    " without its backticks `...`
    " echo system('echo "g (\`'.visual_selected_text.'\`);;" > /tmp/hol_light')
endfunction

function! ApplyVisualSelectionAsTactic() 
    let visual_selected_text = getline("'<")[getpos("'<")[2]-1:getpos("'>")[2]-1]
    let visual_selected_text = substitute(visual_selected_text, '`', '\\`', "g")
    " echom visual_selected_text
    echo system('echo "e ('.visual_selected_text.');;" > /tmp/hol_light')
endfunction

function! PrintGoalStack() range
    echo system('echo "let val_goalstack_ = p ();;" > /tmp/hol_light')
endfunction

:nmap <F2> :call AskHelpForObjectUnderCursor()<CR>
:nmap <F3> :call EvaluateWordUnderCursor()<CR>
:vmap <F4> :call EvaluateVisualSelection()<CR>
:nmap <F5> :call SendExpressionToFifoDevice()<CR>
:vmap <F6> :call EvaluateVisualSelectionAsGoal()<CR>
:vmap <F7> :call ApplyVisualSelectionAsTactic()<CR>
:nmap <F8> :call UndoTacticApplication()<CR>
:nmap <F9> :call PrintGoalStack()<CR>
