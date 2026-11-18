"""Independently replay candidate 8749 trees outside Lean."""

import argparse
from pathlib import Path


def verify(neighbors, words, budget, anchor):
    cursor = 0

    def word():
        nonlocal cursor
        value = words[cursor]
        cursor += 1
        return value

    def odd(row, selected):
        return 0 <= row < len(neighbors) and len(neighbors[row] & selected) % 2 == 1

    def replay(selected, marked):
        opcode = word()
        if opcode == 0:
            row = word()
            return odd(row, selected) and neighbors[row] <= marked
        if opcode == 1:
            count = word()
            packed = set()
            used = set()
            for _ in range(count):
                row = word()
                if row in packed or not odd(row, selected):
                    return False
                packed.add(row)
                available = neighbors[row] - marked
                if used & available:
                    return False
                used.update(available)
            return len(selected) + count > budget
        if opcode == 2:
            column = word()
            if column in marked or not 0 <= column < 3636:
                return False
            decided = marked | {column}
            return replay(selected | {column}, decided) and replay(selected, decided)
        return False

    column = (anchor // 3) * 303 + anchor % 3
    return replay({column}, {column}) and cursor == len(words)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rows", type=Path)
    parser.add_argument("programs", type=Path)
    parser.add_argument("--budget", type=int, required=True)
    parser.add_argument("--begin", type=int, default=0)
    parser.add_argument("--end", type=int, default=36)
    args = parser.parse_args()
    if not 0 <= args.begin < args.end <= 36:
        parser.error("expected a nonempty anchor range within 0–36")
    neighbors = [set(map(int, line.split())) for line in args.rows.read_text().splitlines()]
    if len(neighbors) != 909 or any(len(row) != 12 for row in neighbors):
        parser.error("expected 909 groups of twelve neighbours")
    verified = 0
    with args.programs.open() as programs:
        for anchor, line in enumerate(programs, args.begin):
            words = list(map(int, line.split()))
            if anchor >= args.end or any(not 0 <= word < 4096 for word in words):
                parser.error(f"out-of-range data at anchor {anchor}")
            try:
                accepted = verify(neighbors, words, args.budget, anchor)
            except (IndexError, RecursionError):
                accepted = False
            if not accepted:
                raise SystemExit(f"invalid program for anchor {anchor}")
            verified += 1
            print(f"verified anchor {anchor}", flush=True)
    if verified != args.end - args.begin:
        raise SystemExit(f"verified {verified} programs, expected {args.end - args.begin}")


if __name__ == "__main__":
    main()
