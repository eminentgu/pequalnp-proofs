"""Seven-vertex theta graph in the labels of L-meta-2836."""
VERTICES = (1, 2, 3, 5, 6, 7, 8)
EDGES = ((1, 2), (2, 3), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5))
MASKS = tuple((1 << VERTICES.index(a)) | (1 << VERTICES.index(b)) for a, b in EDGES)
POS = [row for row in range(128) if any(row & edge == edge for edge in MASKS)]
NEG = [row for row in range(128) if row not in POS]
