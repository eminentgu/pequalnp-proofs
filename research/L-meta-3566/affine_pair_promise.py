"""A sub-target circuit for point-line incidence on every input of weight at most two.

Run with plain Python 3. The graph and the circuit are generated independently.
The output is also checked on an explicit independent input of weight three.
"""
from itertools import combinations

Q = 8
N = 2 * Q * Q


def field_mul(left, right):
    product = 0
    for _ in range(3):
        if right & 1:
            product ^= left
        right >>= 1
        left <<= 1
        if left & 8:
            left ^= 0b1011
    return product


def adjacent(point, line):
    if not 0 <= point < 64 <= line < 128:
        return False
    x, y = divmod(point, Q)
    a, b = divmod(line - 64, Q)
    return y == field_mul(x, a) ^ b


class Circuit:
    def __init__(self):
        self.gates = []

    def gate(self, operation, left, right):
        self.gates.append((operation, left, right))
        return N + len(self.gates) - 1

    def fold(self, operation, wires):
        out, *remaining = wires
        for wire in remaining:
            out = self.gate(operation, out, wire)
        return out

    def xor(self, x, y):
        def eq_flag(bit):
            return self.gate('or', self.gate('and', x[0], y[bit]),
                             self.gate('and', x[1], y[1 - bit]))
        return eq_flag(0), eq_flag(1)

    def coord(self, offset, coordinate):
        # On a singleton in this part each bit has exactly one active rail.
        values = [self.fold('or', [offset + v for v in range(64)
                                   if divmod(v, Q)[coordinate] == t]) for t in range(Q)]
        return [[self.fold('or', [values[t] for t in range(Q) if (t >> bit) & 1 == rail])
                 for rail in range(2)] for bit in range(3)]

    def multiply(self, x, a):
        terms = {}
        for i in range(3):
            for j in range(3):
                terms[i, j] = (self.gate('or', x[i][0], a[j][0]),
                               self.gate('and', x[i][1], a[j][1]))
        # z^3 = z+1 and z^4 = z^2+z in F_2[z]/(z^3+z+1).
        powers = [0b001, 0b010, 0b100, 0b011, 0b110]
        product = []
        for bit in range(3):
            first, *rest = [term for (i, j), term in terms.items() if powers[i+j] >> bit & 1]
            total = first
            for term in rest:
                total = self.xor(total, term)
            product.append(total)
        return product

    def build(self):
        x, y, a, b = [self.coord(offset, coordinate)
                      for offset in (0, 64) for coordinate in range(2)]
        flags = [self.gate('or', *coord[0]) for coord in (x, a)]
        for rail, intercept, ordinate in zip(self.multiply(x, a), b, y):
            rhs = self.xor(rail, intercept)
            flags.append(self.gate('or', self.gate('and', rhs[0], ordinate[0]),
                                   self.gate('and', rhs[1], ordinate[1])))
        self.output = self.fold('and', flags)

    def evaluate(self, inputs):
        wires = list(inputs)
        for op, left, right in self.gates:
            wires.append(wires[left] & wires[right] if op == 'and' else wires[left] | wires[right])
        return wires


def check():
    circuit = Circuit()
    circuit.build()
    edges = {(u, v) for u in range(64) for v in range(64, 128) if adjacent(u, v)}
    # A four-cycle would give two points with two common lines.
    neigh = [{v for u, v in edges if u == i} for i in range(64)]
    assert all(len(a & b) <= 1 for a, b in combinations(neigh, 2))
    # Matching of each point (x,y) to the line of slope x through it.
    matching = [(u, 64+(u//Q)*Q+((u % Q) ^ field_mul(u//Q, u//Q))) for u in range(64)]
    assert set(matching) <= edges and len({v for _, v in matching}) == 64
    # All 64 points cover, and the 64 disjoint edges prove minimality.
    assert len(edges) == 512 and len(circuit.gates) < len(edges)+64-1
    rows = [()] + [(v,) for v in range(N)] + list(combinations(range(N), 2))
    inputs = [0] * N
    for k, row in enumerate(rows):
        for v in row:
            inputs[v] |= 1 << k
    wires = circuit.evaluate(inputs)
    expected = sum(1 << i for i, row in enumerate(rows) if row in edges)
    assert wires[circuit.output] == expected
    # Construct an injection from all gates directly into the genuine edge rows.
    indices = [i for i, row in enumerate(rows) if row in edges]
    options = [[i for i in indices if (word >> i) & 1] for word in wires[N:]]
    owner = {}

    def claim(j, visited):
        for i in options[j]:
            if i not in visited:
                visited.add(i)
                if i not in owner or claim(owner[i], visited):
                    owner[i] = j
                    return True
        return False

    assert all(claim(j, set()) for j in range(len(options)))
    assert len(owner) == len(options) == len(set(owner.values()))
    # Points (0,0) and (0,3) are both outside the horizontal line y=1.
    witness = (0, 3, 65)
    assert all(pair not in edges for pair in combinations(witness, 2))
    assert circuit.evaluate([v in witness for v in range(N)])[circuit.output]
    print(f'{len(circuit.gates)} gates, {len(edges)} edges, cover number 64, target 575')
    print(f'All {len(rows)} rows of weight <= 2 agree; {len(owner)} distinct edge labels.')
    print(f'Independent triple accepted: {witness}')


if __name__ == '__main__':
    check()
