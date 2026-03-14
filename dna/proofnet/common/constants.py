import regex as re

REPL_TIMEOUT = 120
TERMINAL_TEXT = ''

INIT_WAIT_TIME = 2

greek = (
    '[\\u03b1-\\u03ba\\u03bc-\\u03c9\\u0391-\\u039f\\u03a1-\\u03a2'
    '\\u03a4-\\u03a9\\u1f00-\\u1ffe]'
)
coptic = '[\\u03ca-\\u03fb]'
letterlike_symbols = '[\\u2100-\\u214f]'
letterlike = f'([a-zA-Z]|{greek}|{coptic}|{letterlike_symbols})'
escaped_ident_part = (
    '\\xab([\\x00-\\x08][\x0b-\x0c]|[\\x0e-\\xaa\\xac-\\xba'
    '\\xbc-\\U0010ffff])*\\xbb'
)
atomic_ident_start = f'({letterlike}|_|{escaped_ident_part})'
subscript = '[\\u2080-\\u2089\\u2090-\\u209c\\u1d62-\\u1d6a]'
superscript = '[\\u2070\\xb9\\xb2-\\xb3\\u2074-\\u2079]'
atomic_ident_rest = (
    f"({atomic_ident_start}|[0-9'\\u207f]|{subscript}|"
    f'\\u271d({superscript})*)'
)
atomic_ident = f'{atomic_ident_start}({atomic_ident_rest})*'
ident = f'{atomic_ident}(\\.{atomic_ident})*'

ident_pattern = re.compile(ident)
