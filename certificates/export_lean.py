"""Deterministic CSV -> Lean converter for the certificate data.

Usage:
    python certificates/export_lean.py --order N --output PATH [--input PATH]

The default input is certificates/brackets.csv (sibling of this script).
Only the standard library is used. Rows for the selected order are emitted
verbatim: scaled integers stay exact decimals and brackets keep the order
they have in the CSV (descending roots). Nothing is normalized.
"""
import argparse
import csv
from pathlib import Path


def fail(message):
    raise SystemExit("export_lean.py: error: " + message)


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, required=True,
                        help='order N to export (selects rows whose first column is N)')
    parser.add_argument('--output', required=True, help='destination Lean file')
    parser.add_argument('--input', default=None,
                        help='source CSV (default: sibling brackets.csv)')
    return parser.parse_args(argv)


def read_selected(order, input_path):
    """Return (rows, source_relative_path). Parse and validate everything first."""
    if not input_path.is_file():
        fail('input file not found: %s' % input_path)

    selected = []
    try:
        with input_path.open(newline='', encoding='utf-8') as handle:
            for lineno, raw in enumerate(csv.reader(handle), start=1):
                if not raw:
                    continue
                try:
                    fields = [int(field) for field in raw]
                except ValueError:
                    fail('malformed integer on line %d' % lineno)
                if fields[0] == order:
                    selected.append((lineno, fields))
    except OSError as exc:
        fail('cannot read input: %s' % exc)

    if not selected:
        fail('missing order %d in %s' % (order, input_path))

    expected = 2 + 2 * (order + 1)  # n, t, then 2*(n+1) bracket endpoints
    for lineno, fields in selected:
        if len(fields) != expected:
            fail('column count on line %d: got %d, expected %d for order %d'
                 % (lineno, len(fields), expected, order))

    previous_t = None
    for lineno, fields in selected:
        t = fields[1]
        if previous_t is not None and t <= previous_t:
            fail('non-increasing t on line %d (%d after %d)'
                 % (lineno, t, previous_t))
        previous_t = t

    rows = []
    for _lineno, fields in selected:
        t = fields[1]
        brackets = fields[2:]
        pairs = [(brackets[i], brackets[i + 1])
                 for i in range(0, len(brackets), 2)]
        rows.append((t, pairs))
    repository = Path(__file__).resolve().parent.parent
    source_path = input_path.resolve()
    source = (source_path.relative_to(repository).as_posix()
              if source_path.is_relative_to(repository) else source_path.name)
    return rows, source


def render(order, rows, source):
    lines = [
        '-- Source: %s' % source,
        '-- order = %d, n = %d' % (order, len(rows)),
        '',
        'import SharpL1.Certificate.Checker',
        '',
        'namespace SharpL1.Certificate.Data',
        '',
        'def order%d : List Row :=' % order,
    ]
    for index, (t, pairs) in enumerate(rows):
        rendered = ', '.join('(%d, %d)' % pair for pair in pairs)
        lead = '  [' if index == 0 else '  ,'
        lines.append('%s⟨%d, [%s]⟩' % (lead, t, rendered))
    lines.append('  ]')
    lines.extend(['', 'end SharpL1.Certificate.Data', ''])
    return '\n'.join(lines)


def main(argv=None):
    args = parse_args(argv)
    input_path = Path(args.input) if args.input is not None else Path(__file__).with_name('brackets.csv')
    rows, source = read_selected(args.order, input_path)
    text = render(args.order, rows, source)

    output_path = Path(args.output)
    try:
        with output_path.open('w', encoding='utf-8', newline='\n') as handle:
            handle.write(text)
    except OSError as exc:
        fail('cannot write output: %s' % exc)

    print('wrote %s: order=%d rows=%d source=%s'
          % (output_path, args.order, len(rows), source))


if __name__ == '__main__':
    main()
