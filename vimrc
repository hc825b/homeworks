" show existing tab with 4 spaces width
set tabstop=4
" when indenting with '>', use 4 spaces width
set shiftwidth=4
" On pressing tab, insert 4 spaces
set expandtab

" Install vim-plug first
" See more detail at https://github.com/junegunn/vim-plug
call plug#begin('~/.vim/vim-plug')
" Syntax highlighting
Plug 'mlr-msft/vim-loves-dafny', {'for': 'dafny'}
Plug 'jlapolla/vim-coq-plugin', {'for': 'coq'}
Plug 'bohlender/vim-smt2', {'for': 'smt2'}
" Automatic ctags generation
"Plug 'ludovicchabant/vim-gutentags', {'for': 'c'}
call plug#end()

" Only do this part when compiled with support for autocommands.
if has("autocmd")
  " Enable file type detection.
  " Use the default filetype settings, so that mail gets 'tw' set to 72,
  " 'cindent' is on in C files, etc.
  " Also load indent files, to automatically do language-dependent indenting.
  filetype plugin indent on

  " For all text files set 'textwidth' to 78 characters and set spell-check.
  autocmd FileType text,markdown,tex,gitcommit setlocal textwidth=80 spell spelllang=en_us

  " Set folding by indent only for Python
  autocmd FileType python setlocal foldmethod=indent
  autocmd FileType * setlocal foldmethod=syntax

endif " has("autocmd")
