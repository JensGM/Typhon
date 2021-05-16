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
        for inst in dis.get_instructions(code):
            if inst.opname == 'LOAD_CONST':
                print(inst.offset, 'LOAD_GENERIC', inst.argval, file=asm)
            elif inst.opname == 'LOAD_FAST':
                print(inst.offset, 'LOAD_GENERIC', inst.argval, file=asm)
            elif inst.opname == 'LOAD_GLOBAL':
                print(inst.offset, 'LOAD_GENERIC', inst.argval, file=asm)
            elif inst.opname == 'LOAD_NAME':
                print(inst.offset, 'LOAD_GENERIC', inst.argval, file=asm)
            else:
                print(inst.offset,
                      inst.opname,
                      inst.argval if inst.argval else inst.arg,
                      file=asm)
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
