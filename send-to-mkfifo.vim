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
    let end = search(";;\w*$") - 1
    echo system('sed -n '.start.','.end.'p '.expand('%').' > /tmp/hol_light')
    let pos = setpos(".", [0, (end+2), 1, 0])
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

:nmap <F2> :call AskHelpForObjectUnderCursor()<CR>
:nmap <F3> :call EvaluateWordUnderCursor()<CR>
:nmap <F5> :call SendExpressionToFifoDevice()<CR>
:nmap <F6> :call UndoTacticApplication()<CR>
