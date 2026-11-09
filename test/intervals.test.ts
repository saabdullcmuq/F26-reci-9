import { describe, expect, it } from 'vitest';
import fc from 'fast-check';
import { mergeIntervals, type Interval } from '../src/intervals';

// Valid intervals are constructed as [start, start + length], so start <= end
// holds by construction.
const intervalWith = (
  start: fc.Arbitrary<number>,
  length: fc.Arbitrary<number>,
): fc.Arbitrary<Interval> => fc.tuple(start, length).map(([s, len]): Interval => [s, s + len]);

const shuffled = <T>(xs: T[]): fc.Arbitrary<T[]> =>
  fc.shuffledSubarray(xs, { minLength: xs.length, maxLength: xs.length });

// Builds intervals left to right, each one starting `gap` after the previous
// one ends. The result is sorted by start.
const walk = (gap: fc.Arbitrary<number>, length: fc.Arbitrary<number>): fc.Arbitrary<Interval[]> =>
  fc
    .tuple(fc.integer({ min: -20, max: 20 }), fc.array(fc.tuple(gap, length), { maxLength: 10 }))
    .map(([origin, steps]) => {
      let cursor = origin;
      return steps.map(([g, len]): Interval => {
        const start = cursor + g;
        cursor = start + len;
        return [start, cursor];
      });
    });

// Small coordinates, so that overlaps, containment, duplicates and shared
// endpoints come up all the time.
const crowded = fc.array(
  intervalWith(fc.integer({ min: -20, max: 20 }), fc.nat(10)),
  { maxLength: 12 },
);

// Neighbours that touch (gap 0) must merge. Neighbours one apart (gap 1) leave
// real numbers between them and must not. Length 0 gives single-point intervals.
const nearlyTouching = walk(fc.constantFrom(0, 1), fc.constantFrom(0, 0, 1, 2, 3)).chain(shuffled);

// Large magnitudes, for anything that only works on small numbers.
const spread = fc.array(
  intervalWith(fc.integer({ min: -1_000_000_000, max: 1_000_000_000 }), fc.nat(1_000_000_000)),
  { maxLength: 8 },
);

const intervalList: fc.Arbitrary<Interval[]> = fc.oneof(crowded, nearlyTouching, spread);

// Sorted intervals with at least 1 between neighbours: nothing overlaps or touches.
const separated = walk(fc.integer({ min: 1, max: 5 }), fc.nat(5));

const nonFinite = fc.constantFrom(NaN, Infinity, -Infinity);
const coordinate = fc.integer({ min: -20, max: 20 });

// Each case breaks the precondition in exactly one way where that is possible.
const invalidInterval: fc.Arbitrary<Interval> = fc.oneof(
  // start > end
  fc.tuple(coordinate, fc.integer({ min: 1, max: 10 })).map(([e, d]): Interval => [e + d, e]),
  // fractional start, still ordered
  fc.tuple(coordinate, fc.nat(10)).map(([s, len]): Interval => [s + 0.5, s + 1 + len]),
  // fractional end, still ordered
  fc.tuple(coordinate, fc.nat(10)).map(([s, len]): Interval => [s, s + len + 0.5]),
  // NaN or an infinity at either end
  fc.tuple(nonFinite, coordinate).map(([x, v]): Interval => [x, v]),
  fc.tuple(coordinate, nonFinite).map(([v, x]): Interval => [v, x]),
);

const covers = (xs: readonly Interval[], p: number): boolean => xs.some(([s, e]) => s <= p && p <= e);

// Coverage can only change at an endpoint, so checking every endpoint and the
// non-integer points on either side of it visits every distinct region,
// including the open gap between [1, 2] and [3, 4].
const probePoints = (...lists: (readonly Interval[])[]): number[] =>
  lists.flat(2).flatMap(e => [e - 0.5, e, e + 0.5]);

const byStart = (a: Interval, b: Interval) => a[0] - b[0];

describe('mergeIntervals', () => {
  // Pattern: invariant. Every input interval lies inside some output interval.
  it('every input interval lies inside some output interval', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const out = mergeIntervals(xs);
        const uncovered = xs.filter(([s, e]) => !out.some(([a, b]) => a <= s && e <= b));
        expect(uncovered).toEqual([]);
      }),
    );
  });

  // Pattern: invariant. The output is well formed, sorted, and consecutive intervals neither overlap nor touch.
  it('output intervals are valid, sorted, and strictly separated', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const out = mergeIntervals(xs);
        for (const [s, e] of out) expect(s).toBeLessThanOrEqual(e);
        for (let i = 0; i + 1 < out.length; i++) expect(out[i]![1]).toBeLessThan(out[i + 1]![0]);
      }),
    );
  });

  // Pattern: invariant. The input array and its intervals are not modified.
  it('does not modify the input', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const before = structuredClone(xs);
        mergeIntervals(xs);
        expect(xs).toEqual(before);
      }),
    );
  });

  // Pattern: differential. A point is covered by the output exactly when a direct check says the input covers it.
  it('covers exactly the same real points as the input', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const out = mergeIntervals(xs);
        const wrong = probePoints(xs, out).filter(p => covers(xs, p) !== covers(out, p));
        expect(wrong).toEqual([]);
      }),
    );
  });

  // Pattern: metamorphic. Reordering the input does not change the output.
  it('ignores input order', () => {
    fc.assert(
      fc.property(intervalList.chain(xs => fc.tuple(fc.constant(xs), shuffled(xs))), ([xs, ys]) => {
        expect(mergeIntervals(ys)).toEqual(mergeIntervals(xs));
      }),
    );
  });

  // Pattern: metamorphic. Duplicating intervals does not change the output.
  it('ignores duplicates', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        expect(mergeIntervals([...xs, ...xs])).toEqual(mergeIntervals(xs));
      }),
    );
  });

  // Pattern: metamorphic. Shifting the input by k shifts the output by k.
  it('commutes with translation', () => {
    fc.assert(
      fc.property(intervalList, fc.integer({ min: -100, max: 100 }), (xs, k) => {
        const shift = (ys: Interval[]) => ys.map(([s, e]): Interval => [s + k, e + k]);
        expect(mergeIntervals(shift(xs))).toEqual(shift(mergeIntervals(xs)));
      }),
    );
  });

  // Pattern: algebraic. Merging is idempotent.
  it('merging twice is the same as merging once', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const once = mergeIntervals(xs);
        expect(mergeIntervals(once)).toEqual(once);
      }),
    );
  });

  // Pattern: algebraic. Merging the parts first gives the same result as merging everything at once.
  it('merging a concatenation matches merging its merged parts', () => {
    fc.assert(
      fc.property(intervalList, intervalList, (xs, ys) => {
        expect(mergeIntervals([...mergeIntervals(xs), ...mergeIntervals(ys)])).toEqual(
          mergeIntervals([...xs, ...ys]),
        );
      }),
    );
  });

  // Pattern: conditional. If nothing overlaps or touches, the output is the input in sorted order.
  it('returns already separated intervals sorted and otherwise unchanged', () => {
    fc.assert(
      fc.property(separated.chain(xs => fc.tuple(fc.constant(xs), shuffled(xs))), ([sorted, xs]) => {
        expect(mergeIntervals(xs)).toEqual(sorted);
      }),
    );
  });

  // Pattern: conditional. Two intervals merge exactly when the later start is at most the earlier end.
  it('merges a pair exactly when it overlaps or touches', () => {
    fc.assert(
      fc.property(
        intervalWith(coordinate, fc.nat(5)),
        intervalWith(coordinate, fc.nat(5)),
        (a, b) => {
          const [first, second] = [a, b].sort(byStart) as [Interval, Interval];
          const expected: Interval[] =
            second[0] <= first[1]
              ? [[first[0], Math.max(first[1], second[1])]]
              : [first, second];
          expect(mergeIntervals([a, b])).toEqual(expected);
        },
      ),
    );
  });

  // Pattern: conditional. An invalid interval anywhere in the input throws a RangeError.
  it('throws a RangeError when any interval is invalid', () => {
    fc.assert(
      fc.property(intervalList, invalidInterval, intervalList, (before, bad, after) => {
        expect(() => mergeIntervals([...before, bad, ...after])).toThrow(RangeError);
      }),
    );
  });

  // Pattern: conditional. The empty list merges to the empty list.
  it('returns [] for []', () => {
    expect(mergeIntervals([])).toEqual([]);
  });
});
