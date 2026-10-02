def is_operand(c):
    return 'a' <= c <= 'z'


def is_operator(c):
    return c in ['~', '&', '|', '>', '#']


def get_precedence(op):
    if op == '~': return 3
    if op == '&' or op == '|': return 2
    if op == '>': return 1
    if op == '#': return 0
    return -1


RIGHT_ASSOCIATIVE = {'~', '>'}  

def has_higher_precedence(stack_op, current_op):
    if current_op in RIGHT_ASSOCIATIVE:
        return get_precedence(stack_op) > get_precedence(current_op)  
    return get_precedence(stack_op) >= get_precedence(current_op)    


def infix_to_postfix(expression):
    stack = []
    postfix = ""
    for c in expression:
        if c == ' ':
            continue
        if is_operand(c):
            postfix += c
        elif c == '(':
            stack.append(c)
        elif c == ')':
            while stack and stack[-1] != '(':
                postfix += stack.pop()
            stack.pop()
        elif is_operator(c):
            while stack and stack[-1] != '(' and has_higher_precedence(stack[-1], c):
                postfix += stack.pop()
            stack.append(c)
    while stack:
        postfix += stack.pop()
    return postfix


def make_node(value, left=None, right=None):
    return {'value': value, 'left': left, 'right': right}


def build_tree(postfix):
    stack = []
    for c in postfix:
        if is_operand(c):
            stack.append(make_node(c))
        elif c == '~':
            child = stack.pop()
            stack.append(make_node('~', left=child))
        elif is_operator(c):
            right = stack.pop()
            left  = stack.pop()
            stack.append(make_node(c, left, right))
    return stack[0]


def print_tree(node, level=0, prefix="Root: "):
    if node is None:
        return
    print(" " * (level * 6) + prefix + node['value'])
    if node['left']:
        print_tree(node['left'],  level + 1, "L--- ")
    if node['right']:
        print_tree(node['right'], level + 1, "R--- ")


def evaluate(node, interpretation):
    if is_operand(node['value']):
        return interpretation[node['value']]
    if node['value'] == '~':
        return not evaluate(node['left'], interpretation)
    left  = evaluate(node['left'],  interpretation)
    right = evaluate(node['right'], interpretation)
    if node['value'] == '&': return left and right
    if node['value'] == '|': return left or right
    if node['value'] == '>': return (not left) or right
    if node['value'] == '#': return left == right

def eliminate_implications(node):
    if node is None:
        return None
    leftt  = eliminate_implications(node['left'])
    rightt = eliminate_implications(node['right'])

    if node['value'] == '>':
        not_left = make_node('~', left=leftt)
        return make_node('|', left=not_left, right=rightt)

    elif node['value'] == '#':
        not_left  = make_node('~', left=leftt)
        not_right = make_node('~', left=rightt)
        part1 = make_node('|', left=not_left,  right=rightt)
        part2 = make_node('|', left=leftt,       right=not_right)
        return make_node('&', left=part1, right=part2)
    else:
        return make_node(node['value'], left=leftt, right=rightt)

def push_negation(node):
    if node is None:
        return None
    
    if node['value'] == '~' and node['left']['value'] == '~':
        return push_negation(node['left']['left'])

    if node['value'] == '~' and node['left']['value'] == '|':
        leftt  = make_node('~', left=node['left']['left'])
        rightt = make_node('~', left=node['left']['right'])
        return push_negation(make_node('&', left=leftt, right=rightt))

    if node['value'] == '~' and node['left']['value'] == '&':
        leftt  = make_node('~', left=node['left']['left'])
        rightt = make_node('~', left=node['left']['right'])
        return push_negation(make_node('|', left=leftt, right=rightt))

    return make_node(node['value'],
                    left=push_negation(node['left']),
                    right=push_negation(node['right']))


def distribute(node):
    if node is None:
        return None

    leftt  = distribute(node['left'])
    rightt = distribute(node['right'])

    if node['value'] == '|':
        # A ∨ (B ∧ C)  => (A ∨ B) ∧ (A ∨ C)
        if rightt is not None and rightt['value'] == '&':
            new_left  = distribute(make_node('|', left=leftt, right=rightt['left']))
            new_right = distribute(make_node('|', left=leftt, right=rightt['right']))
            return make_node('&', left=new_left, right=new_right)
        # (A ∧ B) ∨ C  => (A ∨ C) ∧ (B ∨ C)
        if leftt is not None and leftt['value'] == '&':
            new_left  = distribute(make_node('|', left=leftt['left'],  right=rightt))
            new_right = distribute(make_node('|', left=leftt['right'], right=rightt))
            return make_node('&', left=new_left, right=new_right)

    return make_node(node['value'], left=leftt, right=rightt)

def get_literals(node, literals):
    if node is None:
        return
    if node['value'] == '|':
        get_literals(node['left'],  literals)
        get_literals(node['right'], literals)
    elif node['value'] == '~':
        literals.append('~' + node['left']['value'])
    else:
        literals.append(node['value'])


def extract_clauses(node, clauses):
    if node is None:
        return
    if node['value'] == '&':
        extract_clauses(node['left'],  clauses)
        extract_clauses(node['right'], clauses)
    else:
        literals = []
        get_literals(node, literals)
        clauses.append(literals)

def simplify(clauses):
    result = []
    for clause in clauses:
        clause = list(dict.fromkeys(clause))
        tautology = False
        for lit in clause:
            opposite = lit[1:] if lit.startswith('~') else '~' + lit
            if opposite in clause:
                tautology = True
                break
        if tautology:
            continue
        if clause not in result:
            result.append(clause)
    return result


# ===== MAIN =====

expr = input("Enter formula (use ~, &, |, >, #): ")

postfix = infix_to_postfix(expr)
print("\n1. Postfix =", postfix)

tree = build_tree(postfix)
print("\n2. Tree:")
print_tree(tree)

variables = sorted(set(c for c in expr if is_operand(c)))
print("\n3. Enter truth values (V or F):")
interpretation = {}
for var in variables:
    val = input(f"   {var} = ").strip().upper()
    interpretation[var] = (val == 'V')

result = evaluate(tree, interpretation)
print("\nResult:", "V (Vrai)" if result else "F (Faux)")

tree2 = eliminate_implications(tree)
print("\n--- After eliminating implications ---")
print_tree(tree2)

tree3 = push_negation(tree2)
print("\n--- After pushing negations ---")  
print_tree(tree3)

tree4 = distribute(tree3)
print("\n--- After distributing ---")
print_tree(tree4)

clauses = []
extract_clauses(tree4, clauses)
print("\n--- Before simplification ---")
for i, clause in enumerate(clauses):
    print(f"  C{i+1}: {{ {', '.join(clause)} }}")
simplified = simplify(clauses)
print("\n--- After simplification ---")
if not simplified:
    print("  Formula is a tautology")
else:
    for i, clause in enumerate(simplified):
        print(f"  C{i+1}: {{ {', '.join(clause)} }}")
