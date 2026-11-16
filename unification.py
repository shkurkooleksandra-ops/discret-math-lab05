import re
import sys
from collections import deque

VARIABLES = frozenset({"x", "y", "z", "u", "v", "w"})
EOF = "кінець вводу"
EXAMPLE = "python3 unification.py 'P(a, y)' 'P(x, f(b))'"
TOKEN_RE = re.compile(
    r"\s+"
    r"|(?P<TOKEN>[A-Za-z_][A-Za-z_0-9]*|[(),])"
    r"|(?P<ERROR>.)",
    re.DOTALL
)


def input_error(message):
    raise ValueError(
        f"Помилка: {message}\n\n"
        f"Приклад запуску:\n{EXAMPLE}"
    )


def tokenize(text):
    tokens = []
    for match in TOKEN_RE.finditer(text):
        if match.lastgroup == "ERROR":
            input_error(f"Недопустимий символ {match.group()!r}.")
        elif match.lastgroup == "TOKEN":
            tokens.append(match.group())
    return tokens


def parse_predicate(text, variables=VARIABLES):
    tokens = tokenize(text) + [EOF]
    index = 0

    def peek():
        return tokens[index]

    def consume(expected=None):
        nonlocal index
        token = peek()
        if expected is not None and token != expected:
            input_error(f"Очікується {expected!r}, отримано {token!r}.")
        index += 1
        return token

    def name():
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", peek()):
            input_error(f"Очікується ім'я, отримано {peek()!r}.")
        return consume()

    def arguments():
        result = []
        if peek() != ")":
            result.append(term())
            while peek() == ",":
                consume(",")
                result.append(term())
        consume(")")
        return tuple(result)

    def term():
        symbol = name()
        if peek() == "(":
            if symbol in variables:
                input_error(f"Ім'я змінної {symbol!r} не може бути ім'ям функції.")
            consume("(")
            args = arguments()
            return (symbol, args) if args else symbol
        return symbol

    predicate_name = name()
    consume("(")
    predicate = (predicate_name, arguments())
    if peek() != EOF:
        input_error(f"Зайвий токен {peek()!r} після предиката.")
    return predicate


def is_variable(term, variables=VARIABLES):
    return isinstance(term, str) and term in variables


def format_term(term):
    if isinstance(term, str):
        return term
    name, args = term
    return f"{name}({', '.join(map(format_term, args))})"


def format_predicate(predicate):
    return format_term(predicate)


def format_substitution(substitution):
    return "{" + ", ".join(
        f"{name} ↦ {format_term(value)}"
        for name, value in substitution.items()
    ) + "}"


def format_equations(equations):
    return "; ".join(
        f"{format_term(left)} = {format_term(right)}"
        for left, right in equations
    ) or "немає"


def apply_substitution(term, substitution):
    if isinstance(term, str):
        value = substitution.get(term)
        return term if value is None else apply_substitution(value, substitution)
    name, args = term
    return (
        name,
        tuple(apply_substitution(arg, substitution) for arg in args)
    )


def apply_to_predicate(predicate, substitution):
    return apply_substitution(predicate, substitution)


def occurs(variable, term):
    if isinstance(term, str):
        return variable == term
    return any(occurs(variable, arg) for arg in term[1])


def extend_substitution(substitution, variable, term):
    replacement = {variable: term}
    result = {
        name: apply_substitution(value, replacement)
        for name, value in substitution.items()
    }
    result[variable] = term
    return result


def unify(first_text, second_text, variables=VARIABLES):
    first = parse_predicate(first_text, variables)
    second = parse_predicate(second_text, variables)
    print(f"Перший предикат: {format_predicate(first)}")
    print(f"Другий предикат: {format_predicate(second)}")
    print(f"Змінні: {', '.join(sorted(variables))}")
    print("Інші імена без аргументів — константи.")

    def failure(reason):
        print(f"\nУніфікація неможлива: {reason}")
        return None

    if first[0] != second[0]:
        return failure(f"різні назви предикатів: {first[0]} та {second[0]}.")
    if len(first[1]) != len(second[1]):
        return failure(
            f"різна кількість аргументів: {len(first[1])} та {len(second[1])}."
        )

    equations = deque(zip(first[1], second[1]))
    substitution = {}
    step = 0
    print(f"\nПочаткові рівняння: {format_equations(equations)}")

    while equations:
        left, right = equations.popleft()
        left = apply_substitution(left, substitution)
        right = apply_substitution(right, substitution)
        step += 1
        print(f"\nКрок {step}: {format_term(left)} = {format_term(right)}")

        if left == right:
            print("Терми однакові. Вилучаємо рівняння.")

        elif is_variable(left, variables) or is_variable(right, variables):
            if not is_variable(left, variables):
                left, right = right, left
                print(f"Переставляємо: {format_term(left)} = {format_term(right)}")
            variable = left
            if occurs(variable, right):
                return failure(
                    f"змінна {variable} входить у терм {format_term(right)} "
                    "(перевірка входження, occurs check)."
                )
            print(f"Нова підстановка: {variable} ↦ {format_term(right)}")
            substitution = extend_substitution(substitution, variable, right)
            equations = deque(
                (apply_substitution(a, substitution), apply_substitution(b, substitution))
                for a, b in equations
            )

        else:
            if isinstance(left, str) and isinstance(right, str):
                return failure(f"різні константи: {left} та {right}.")
            if isinstance(left, str) or isinstance(right, str):
                return failure(
                    f"константа і складений терм не збігаються: "
                    f"{format_term(left)} та {format_term(right)}."
                )
            left_name, left_args = left
            right_name, right_args = right
            if left_name != right_name:
                return failure(f"різні назви функцій: {left_name} та {right_name}.")
            if len(left_args) != len(right_args):
                return failure(
                    f"функція {left_name} має різну кількість аргументів: "
                    f"{len(left_args)} та {len(right_args)}."
                )
            pairs = list(zip(left_args, right_args))
            print(f"Порівнюємо відповідні аргументи: {format_equations(pairs)}")
            equations.extendleft(reversed(pairs))

        print(f"σ = {format_substitution(substitution)}")
        print(f"Залишилися рівняння: {format_equations(equations)}")

    unified = apply_to_predicate(first, substitution)
    print(f"\nНайзагальніший уніфікатор: σ = {format_substitution(substitution)}")
    print(f"Перший предикат після підстановки: {format_predicate(unified)}")
    print(
        "Другий предикат після підстановки: "
        f"{format_predicate(apply_to_predicate(second, substitution))}"
    )
    return substitution


first_text = input("Перший предикат: ")
second_text = input("Другий предикат: ")
unify(first_text, second_text)
