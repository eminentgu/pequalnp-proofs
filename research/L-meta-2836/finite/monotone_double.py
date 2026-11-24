"""Run the adjacent monotone checker unchanged except for the selected input bank."""
from pathlib import Path
from importlib.util import module_from_spec,spec_from_file_location

path=Path(__file__).resolve().parents[1]/'triple'/'monotone_search.py'
spec=spec_from_file_location('triple_monotone',path)
search=module_from_spec(spec)
spec.loader.exec_module(search)
physical=search.RAW
for encoding in ('043','401','405'):
    center, first, second = map(int,encoding)
    search.RAW = tuple(v for j,v in enumerate(physical) if j!=center) + (
        physical[center] | physical[first],physical[center] | physical[second])
    print("Double-OR",encoding, flush=True)
    assert not search.solve(None,13)
search.RAW = physical
print("Raw inputs",flush=True)
assert not search.solve(None,13)
