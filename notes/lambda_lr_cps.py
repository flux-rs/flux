from pygments.lexer import RegexLexer, words
from pygments.token import *

class CustomLexer(RegexLexer):
    tokens = {
        'root': [
            (words(('fn', 'ret', 'if', 'then', 'else', 'let', 'in', 'letcont', 'jump', 'abort', 'call', 'own', 'ref'), suffix=r'\b'), Keyword),
            (r'//.*', Comment),
            (r'.', Text)
        ]
    }


