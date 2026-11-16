import re
import sys

AND = "/\\"
OR = "\\/"
EXAMPLE = r"(p /\ ~q) -> r, (q \/ ~r) -> r, p \/ q, ~h |- (p -> r)"
TOKEN_RE = re.compile(
    r"\s+"
    r"|(?P<TOKEN>\|-|->|\\/|/\\|[~(),a-z])"
    r"|(?P<ERROR>.)",
    re.DOTALL
)
EOF = "end_of_input"


def input_error(message):
    raise ValueError(
        f"Помилка: {message}\n\n"
        f"Правильний приклад вводу:\n{EXAMPLE}"
    )


def tokenize(text):
    tokens = []

    for match in TOKEN_RE.finditer(text):
        if match.lastgroup == "ERROR":
            input_error(f"Недопустимий символ {match.group()!r}.")
        elif match.lastgroup == "TOKEN":
            tokens.append(match.group())

    return tokens


def parse_input(text):
    tokens = tokenize(text) + [EOF]
    index = 0
    priorities = {"->": 1, OR: 2, AND: 3}

    def peek():
        return tokens[index]

    def consume(expected=None):
        nonlocal index
        token = peek()
        if expected is not None and token != expected:
            input_error(f"Очікується {expected!r}, отримано {token!r}.")
        index += 1
        return token

    def expression(min_priority=1):
        token = peek()
        if token == "~":
            consume()
            left = ("~", expression(4))
        elif token == "(":
            consume()
            left = expression()
            consume(")")
        elif re.fullmatch(r"[a-z]", token):
            left = consume()
        else:
            input_error(f"Очікується змінна a-z, '~' або '(', отримано {token!r}.")

        while priorities.get(peek(), 0) >= min_priority:
            operation = consume()
            priority = priorities[operation]

            next_priority = priority if operation == "->" else priority + 1
            left = (operation, left, expression(next_priority))
        return left

    premises = [expression()]
    while peek() == ",":
        consume(",")
        premises.append(expression())
    consume("|-")
    goal = expression()
    if peek() != EOF:
        input_error(f"Зайвий токен {peek()!r} після висновку.")
    return premises, goal


def format_formula(node):
    if isinstance(node, list):
        return ", ".join(format_formula(formula) for formula in node)
    if isinstance(node, str):
        return node
    if node[0] == "~":
        return "~" + format_formula(node[1])
    return f"({format_formula(node[1])} {node[0]} {format_formula(node[2])})"


def eliminate_implications(node):
    if isinstance(node, str):
        return node
    if node[0] == "~":
        return ("~", eliminate_implications(node[1]))
    left = eliminate_implications(node[1])
    right = eliminate_implications(node[2])
    if node[0] == "->":
        return (OR, ("~", left), right)
    return (node[0], left, right)


def to_nnf(node, negated=False):
    if isinstance(node, str):
        return ("~", node) if negated else node
    operation = node[0]
    if operation == "~":
        return to_nnf(node[1], not negated)
    if operation not in (AND, OR):
        raise ValueError("потрібно усунути імплікації.")
    if negated:
        if operation == AND:
            operation = OR
        else:
            operation = AND
    return (operation, to_nnf(node[1], negated), to_nnf(node[2], negated))


def simplify_formula(node):
    if isinstance(node, str) or node[0] == "~":
        return node
    left = simplify_formula(node[1])
    right = simplify_formula(node[2])
    if left == right:
        return left
    return (node[0], left, right)


def opposite(literal):
    return literal[1:] if literal.startswith("~") else "~" + literal


def simplify_clause(literals):
    unique = set(literals)
    if any(opposite(literal) in unique for literal in unique):
        return None
    return tuple(sorted(unique))


def to_cnf(node):
    if isinstance(node, str):
        return [(node,)]
    if node[0] == "~":
        return [("~" + node[1],)]
    left = to_cnf(node[1])
    right = to_cnf(node[2])
    if node[0] == AND:
        return left + right
    result = []
    for first in left:
        for second in right:
            clause = simplify_clause(first + second)
            if clause is not None:
                result.append(clause)
    return result


def format_clause(clause):
    return f" {OR} ".join(clause) if clause else "∅"


def find_resolvable_pairs(clauses):
    right = 1
    while right < len(clauses):
        for left in range(right):
            for literal in clauses[left]:
                if opposite(literal) in clauses[right]:
                    yield left, right, literal
        right += 1


#
def resolve_pair(left, right, literal):
    return (
            tuple(value for value in left if value != literal)
            + tuple(value for value in right if value != opposite(literal))
    )


def prove(text):
    premises, goal = parse_input(text)
    formulas = premises + [("~", goal)]
    clauses = []
    known = set()
    print(f"{format_formula(premises)} |- {format_formula(goal)}")
    print(f"Додаємо заперечення: {format_formula(('~', goal))}")

    for index, source in enumerate(formulas):
        without_arrows = eliminate_implications(source)
        print("\n")
        print(without_arrows)
        nnf = simplify_formula(to_nnf(without_arrows))
        print(f"nnf: {nnf}")
        cnf = to_cnf(nnf)
        print(f"cnf: {cnf}")
        label = f"Передумова {index + 1}" if index < len(premises) else "Заперечення передумови"
        print(f"{label}: {format_formula(source)}")
        print(f"Без імплікації: {format_formula(without_arrows)}")
        print(f"Після спрощення: {format_formula(nnf)}")
        for raw in cnf:
            clause = simplify_clause(raw)
            if clause is not None and clause not in known:
                known.add(clause)
                clauses.append(clause)
                print(f"C{len(clauses)} = {format_clause(clause)}")

    print("\nРезолюція:")
    step = 0
    for left, right, literal in find_resolvable_pairs(clauses):
        raw = resolve_pair(clauses[left], clauses[right], literal)
        result = simplify_clause(raw)
        if result is None or result in known:
            continue
        known.add(result)
        clauses.append(result)
        step += 1
        print(f"\nКрок {step}: C{left + 1} + C{right + 1}")
        print(
            f"C{left + 1} ({format_clause(clauses[left])}) + "
            f"C{right + 1} ({format_clause(clauses[right])})"
        )
        print(f"Вилучаємо: {literal} та {opposite(literal)}")
        if len(raw) != len(result):
            print(f"Прибираємо повтори: {format_clause(raw)} = {format_clause(result)}")
        print(f"C{len(clauses)} = {format_clause(result)}")
        if not result:
            print("\nОтримано порожній диз'юнкт. Висновок доведено.")
            return True

    print("\nУсі можливі резолюції опрацьовано. Висновок не випливає із передумов.")
    return False


if __name__ == "__main__":
    prove("(p /\\ ~q) -> r, (q /\\ ~r) -> r |- p -> r")
