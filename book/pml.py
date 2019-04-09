#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# This file contains provides a Pygments lexer for PML, that may be used to
# display PML code in LaTeX documents thanks to the “minted” package.
#
# Requirements: pygmentize >= 2.2.0 (check with “pygmentize -V”)
#
# \usepackage{minted}
# \begin{minted}{pml.py:PMLLexer -x}
#   ...
# \end{minted}

from pygments.lexer import RegexLexer, bygroups, combined, include
from pygments.token import Text, Comment, Operator, Keyword, Name, String
from pygments.token import Number, Punctuation, Whitespace

class PMLLexer(RegexLexer):
    """
    A Pygments lexer for the PML language
    """

    name = 'PML'
    aliases = ['pml']
    filenames = ['*.pml']

    keywords = [
      'assert', 'assume', 'because', 'bool', 'by', 'case', 'check', 'corec',
      'deduce', 'delim', 'def', 'else', 'eqns', 'fix', 'for', 'fun', 'if',
      'include', 'infix', 'know', 'let', 'of', 'print', 'qed', 'rec',
      'restore', 'save', 'set', 'show', 'showing', 'sort', 'such', 'suppose',
      'take', 'that', 'type', 'unsafe', 'use', 'using', 'val'
    ]

    special = [
      '∀', '∃', ',', '∈', '⇒', '→', '✂', '=', '≡', '{', '}', '\(', '\)', '\[',
      '\]', '\:', '\.', ';', '⟨', '⟩'
    ]

    tokens = {
        'root': [
            (r'\s+', Text),
            (r'\b(%s)\b' % '|'.join(keywords), Keyword),
            (r'(%s)' % '|'.join(special), Keyword),
            (r'//.*$', Comment.Single),
            (r'\w+', Name.Variable),
        ]
    }
