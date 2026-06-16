import ast
import dis
import inspect
import io
import string
import textwrap


def function_source(func):
    """Function Source
    Get the source code of a function. Cannot be done on dynamically generated
    functions.
    Returns
    -------
    str
        Function source code
    """
    source = inspect.getsource(func)
    dedent = textwrap.dedent(source)
    return dedent


def function_ast(func):
    """Function AST
    Get an abstract syntax tree of a function
    Returns
    -------
    ast.Module
        Abstract syntax tree of the function
    """
    src = function_source(func)
    return ast.parse(src)


def is_lambda(λ, _λname=(lambda:_).__name__):
    return λ.__name__ == _λname


def lambda_sources(λ):
    raise NotImplementedError


def lambda_ast(λ):
    """
    This is complicated.

    inspired by [1].

    .. [1] https://gist.github.com/Xion/617c1496ff45f3673a5692c3b0e3f75a
    """
    def explode(code):
        asm = io.StringIO()
        seq = 0
        for inst in dis.get_instructions(code):
            # Skip opcodes that have no semantic meaning for matching
            if inst.opname in ('RESUME', 'COPY_FREE_VARS',
                                'PUSH_NULL', 'NOT_TAKEN'):
                continue
            if inst.opname in ('LOAD_CONST', 'LOAD_SMALL_INT'):
                print(seq, 'LOAD_GENERIC', inst.argval, file=asm)
            elif inst.opname in ('LOAD_FAST', 'LOAD_FAST_BORROW',
                                 'LOAD_FAST_LOAD_FAST'):
                print(seq, 'LOAD_GENERIC', inst.argval, file=asm)
            elif inst.opname in ('LOAD_GLOBAL',):
                print(seq, 'LOAD_GENERIC', inst.argval, file=asm)
            elif inst.opname in ('LOAD_NAME', 'LOAD_DEREF'):
                print(seq, 'LOAD_GENERIC', inst.argval, file=asm)
            else:
                # For jump instructions, argval is a byte offset that
                # differs between compilation modes — use opname only
                argval = inst.argval if inst.argval else inst.arg
                if inst.opname.startswith(('POP_JUMP_', 'JUMP_')):
                    argval = '_'
                print(seq, inst.opname, argval, file=asm)
            seq += 1
        asm.seek(0)
        return asm.read()

    source = function_source(λ)
    tree = ast.parse(source)

    Λ = [node for node in ast.walk(tree) if isinstance(node, ast.Lambda)]

    for λnode in Λ:
        λsrc = source[λnode.col_offset:]
        λsrc_body = source[λnode.body.col_offset:]

        # Sometimes python will give you the wrong col_offset if there are line
        # line breaks in lambdas.
        λsrc_body = λsrc_body.lstrip(string.whitespace + ':')

        min_length = len('lambda:_')  # shortest possible lambda expression

        while len(λsrc) > min_length:
            try:
                code = compile(λsrc_body, '<ast>', 'eval')

                if explode(code) == explode(λ.__code__):
                    return ast.parse(λsrc)
            except SyntaxError:
                pass
            λsrc = λsrc[:-1]
            λsrc_body = λsrc_body[:-1]

    raise ValueError('Unable to extract lambda source code')
