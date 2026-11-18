"""Exact JSON value equality: no Python bool/int/float coercion."""
def same_value(left, right):
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return left.keys() == right.keys() and all(same_value(left[k], right[k]) for k in left)
    if type(left) is list:
        return len(left) == len(right) and all(same_value(a, b) for a, b in zip(left, right))
    return left == right
