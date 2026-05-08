"""
Tests for pure algorithmic functions from `sero` (Minesweeper Solver).

Each test class contains a Python re-implementation of the corresponding
Lua function, followed by unit tests that verify the expected behaviour
described by the implementation in `sero`.

Functions tested (all are pure / side-effect-free):
  - is_number          (isNumber)
  - make_key           (key)
  - cluster_sorted     (clusterSorted)
  - median_lua         (median)
  - typical_spacing    (typicalSpacing)
  - nearest_index      (nearestIndex)
  - is_covered_cell    (isCoveredCell)
  - n_choose_k         (nCk)
  - make_bitmasks_set  (makeBitmasks – "set" mode)
  - is_subset_mask_set (isSubsetMask – "set" mode)
  - diff_mask_set      (diffMask – "set" mode)
  - constraint_key     (constraintKeyForComp)
  - fmt_pct            (fmtPct)
  - compute_parts_sig  (computePartsSignature)
  - enumerate_component (enumerateComponent)
"""

import math
import unittest
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Python implementations mirroring the Lua functions in `sero`
# ---------------------------------------------------------------------------

def is_number(s: str) -> bool:
    """Lua: isNumber(str) – returns True if str can be converted to a number."""
    try:
        float(s)
        return True
    except (ValueError, TypeError):
        return False


def make_key(ix: Any, iz: Any) -> str:
    """Lua: key(ix, iz) – 'ix:iz' string."""
    return f"{ix}:{iz}"


def cluster_sorted(sorted_list: List[float], epsilon: float) -> List[float]:
    """
    Lua: clusterSorted(sorted_list, epsilon)

    Groups consecutive elements within `epsilon` of a running cluster centre.
    Returns a list of cluster centres (one per group).
    """
    clusters: List[float] = []
    if not sorted_list:
        return clusters

    current_center = sorted_list[0]
    current_count = 1

    for v in sorted_list[1:]:
        if abs(v - current_center) <= epsilon:
            current_count += 1
            current_center = current_center + (v - current_center) / current_count
        else:
            clusters.append(current_center)
            current_center = v
            current_count = 1

    clusters.append(current_center)
    return clusters


def median_lua(tbl: List[float]) -> Optional[float]:
    """
    Lua: median(tbl)

    Sorts the list in-place and returns the element at 1-based index
    floor((n+1)/2) (i.e. lower median for even-length lists).
    Returns None for an empty list.
    """
    if not tbl:
        return None
    tbl_sorted = sorted(tbl)
    mid = math.floor((len(tbl_sorted) + 1) / 2)  # 1-based
    return tbl_sorted[mid - 1]                     # convert to 0-based


def typical_spacing(sorted_centers: List[float]) -> float:
    """
    Lua: typicalSpacing(sorted_centers)

    Returns the median of consecutive differences; falls back to 4 if fewer
    than 2 centres.
    """
    if len(sorted_centers) < 2:
        return 4.0
    diffs = [abs(sorted_centers[i] - sorted_centers[i - 1])
             for i in range(1, len(sorted_centers))]
    return median_lua(diffs) or 4.0


def nearest_index(v: float, centers: List[float]) -> int:
    """
    Lua: nearestIndex(v, centers)

    Binary search returning 0-based index of the element nearest to v.
    Returns -1 for an empty list.

    Note: the Lua implementation is 1-based internally and returns mid-1 on
    exact match (0-based), then scans lo-1, lo, lo+1 for nearest.
    """
    n = len(centers)
    if n == 0:
        return -1

    lo, hi = 0, n - 1  # 0-based for Python, mirrors 1-based Lua after adjustment
    # Replicate the Lua algorithm exactly (1-based indices, subtract 1 at end)
    lo_lua, hi_lua = 1, n
    while lo_lua <= hi_lua:
        mid = math.floor((lo_lua + hi_lua) / 2)
        cm = centers[mid - 1]
        if cm == v:
            return mid - 1   # exact match → 0-based
        if cm < v:
            lo_lua = mid + 1
        else:
            hi_lua = mid - 1

    best_i = 1
    best_d = math.inf
    for candidate in [lo_lua - 1, lo_lua, lo_lua + 1]:
        if 1 <= candidate <= n:
            d = abs(v - centers[candidate - 1])
            if d < best_d:
                best_d = d
                best_i = candidate

    return best_i - 1  # convert to 0-based


def is_covered_cell(cell: Optional[Dict]) -> bool:
    """
    Lua: isCoveredCell(cell)

    Returns False if cell is None.
    Returns False if cell.state == "number".
    Returns True  if cell.covered is not explicitly False.
    """
    if cell is None:
        return False
    if cell.get("state") == "number":
        return False
    return cell.get("covered") is not False


def n_choose_k(n: int, k: int) -> float:
    """
    Lua: nCk(n, k)

    Binomial coefficient using iterative multiplication, matching the Lua
    floating-point implementation exactly.
    """
    if k < 0 or k > n:
        return 0
    if k == 0 or k == n:
        return 1
    if k > n - k:
        k = n - k

    res = 1.0
    for i in range(1, k + 1):
        res = res * (n - (k - i))
        res = res / i
    return res


# --- Bitmask helpers (set mode only – no bit32/bit available in Python) ---

def make_bitmasks_set(membership_lists: List[List[int]]) -> List[Dict[int, bool]]:
    """
    Lua: makeBitmasks(...) when neither bit32 nor bit is available → "set" mode.

    Each mask is a dict {idx: True} for every 1-based index in the list.
    """
    masks = []
    for lst in membership_lists:
        s: Dict[int, bool] = {}
        for idx in lst:
            s[idx] = True
        masks.append(s)
    return masks


def is_subset_mask_set(A: Dict[int, bool], B: Dict[int, bool]) -> bool:
    """
    Lua: isSubsetMask(A, B, "set")

    A ⊆ B: every key in A must also exist in B.
    """
    for k in A:
        if k not in B:
            return False
    return True


def diff_mask_set(A: Dict[int, bool], B: Dict[int, bool]) -> List[int]:
    """
    Lua: diffMask(A, B, "set")

    Returns indices that are in B but NOT in A.
    """
    return [idx for idx in B if idx not in A]


def constraint_key(constraints: List[Dict]) -> str:
    """
    Lua: constraintKeyForComp(constraints)

    For each constraint sorts its idxs, formats as "sorted_idxs:rem",
    then sorts all parts and joins with "|".
    """
    parts = []
    for c in constraints:
        idxs = sorted(c["idxs"])
        parts.append(",".join(str(i) for i in idxs) + ":" + str(c["rem"]))
    parts.sort()
    return "|".join(parts)


def fmt_pct(p: float) -> str:
    """
    Lua: fmtPct(p)

    Rounds p to the nearest 1/20 (5%) then formats as an integer percentage.
    """
    q = math.floor(p * 20 + 0.5) / 20
    return f"{math.floor(q * 100 + 0.5)}%"


def compute_parts_signature(parts: List[Dict]) -> str:
    """
    Lua: computePartsSignature(parts)

    Samples up to 12 evenly-spaced parts (by index), packs their quantised
    X/Z positions plus the total count into a "|"-separated string.
    """
    n = len(parts)
    if n == 0:
        return "0"

    step = max(1, math.floor(n / 12))
    acc = [str(n)]
    k = 1

    i = 0
    while i < n:
        p = parts[i]
        pos = p.get("Position")
        if pos:
            x = math.floor(pos["X"] * 10 + 0.5)
            z = math.floor(pos["Z"] * 10 + 0.5)
            acc.append(f"{x},{z}")
        k += 1
        if k > 12:
            break
        i += step

    return "|".join(acc)


def enumerate_component(
    comp_cells: List[Any],
    constraints: List[Dict],
    solution_cap: Optional[int],
) -> Tuple[int, List[int], int, int, Dict[int, int], List[Dict[int, int]], bool]:
    """
    Lua: enumerateComponent(compCells, constraints, solutionCap)

    Exhaustive backtracking solver. Returns:
      (total, counts_per_var, min_m, max_m, pmf, counts_per_var_per_k, capped)
    """
    n = len(comp_cells)
    counts_per_var = [0] * n
    counts_per_var_per_k: List[Dict[int, int]] = [{} for _ in range(n)]

    # Build var → constraint index mapping (1-based constraint indices)
    var_constraints: List[List[int]] = [[] for _ in range(n)]
    for ci, c in enumerate(constraints, start=1):
        for vi in c["idxs"]:
            var_constraints[vi - 1].append(ci)

    # Ordering heuristic: more constraints first, then tighter constraints
    order = list(range(n))  # 0-based variable indices

    def tightness(var_idx: int) -> float:
        vcons = var_constraints[var_idx]
        if not vcons:
            return math.inf
        min_t = math.inf
        for ci in vcons:
            c = constraints[ci - 1]
            n_idxs = len(c["idxs"])
            t = min(c["rem"], n_idxs - c["rem"])
            if t < min_t:
                min_t = t
        return min_t

    order.sort(
        key=lambda a: (-len(var_constraints[a]), tightness(a))
    )

    cur_assigned = [0] * len(constraints)
    cur_unassigned = [len(c["idxs"]) for c in constraints]
    assignment = [0] * n

    total = 0
    min_seen: Optional[int] = None
    max_seen: Optional[int] = None
    pmf: Dict[int, int] = {}
    stop = False
    capped = False

    def recurse(depth: int, cur_mines: int) -> None:
        nonlocal total, min_seen, max_seen, stop, capped

        if stop:
            return

        if depth >= n:
            total += 1
            pmf[cur_mines] = pmf.get(cur_mines, 0) + 1
            if min_seen is None or cur_mines < min_seen:
                min_seen = cur_mines
            if max_seen is None or cur_mines > max_seen:
                max_seen = cur_mines

            for i in range(n):
                if assignment[i] == 1:
                    counts_per_var[i] += 1
                    cpvk = counts_per_var_per_k[i]
                    cpvk[cur_mines] = cpvk.get(cur_mines, 0) + 1

            if solution_cap is not None and total >= solution_cap:
                stop = True
                capped = True
            return

        var = order[depth]
        vcons = var_constraints[var]

        # Try value = 0
        ok0 = True
        for ci in vcons:
            cur_unassigned[ci - 1] -= 1
            rem = constraints[ci - 1]["rem"]
            if cur_assigned[ci - 1] > rem or \
               (cur_assigned[ci - 1] + cur_unassigned[ci - 1]) < rem:
                ok0 = False
        if ok0:
            assignment[var] = 0
            recurse(depth + 1, cur_mines)
        for ci in vcons:
            cur_unassigned[ci - 1] += 1
        if stop:
            return

        # Try value = 1
        ok1 = True
        for ci in vcons:
            cur_unassigned[ci - 1] -= 1
            cur_assigned[ci - 1] += 1
            rem = constraints[ci - 1]["rem"]
            if cur_assigned[ci - 1] > rem or \
               (cur_assigned[ci - 1] + cur_unassigned[ci - 1]) < rem:
                ok1 = False
        if ok1:
            assignment[var] = 1
            recurse(depth + 1, cur_mines + 1)
        for ci in vcons:
            cur_unassigned[ci - 1] += 1
            cur_assigned[ci - 1] -= 1
        assignment[var] = 0

    recurse(0, 0)

    # Fill pmf gaps (Lua fills 0..n)
    pmf.setdefault(0, 0)
    for k in range(1, n + 1):
        pmf.setdefault(k, 0)

    return (
        total,
        counts_per_var,
        min_seen if min_seen is not None else 0,
        max_seen if max_seen is not None else 0,
        pmf,
        counts_per_var_per_k,
        capped,
    )


# ===========================================================================
# Test classes
# ===========================================================================

class TestIsNumber(unittest.TestCase):
    def test_integer_string(self):
        self.assertTrue(is_number("42"))

    def test_float_string(self):
        self.assertTrue(is_number("3.14"))

    def test_negative_string(self):
        self.assertTrue(is_number("-7"))

    def test_zero_string(self):
        self.assertTrue(is_number("0"))

    def test_scientific_notation(self):
        self.assertTrue(is_number("1e5"))

    def test_empty_string_is_false(self):
        self.assertFalse(is_number(""))

    def test_alpha_string_is_false(self):
        self.assertFalse(is_number("abc"))

    def test_mixed_alphanumeric_is_false(self):
        self.assertFalse(is_number("12abc"))

    def test_whitespace_only_is_false(self):
        # Python float(" ") raises ValueError; Lua tonumber(" ") returns nil
        self.assertFalse(is_number("  "))

    def test_single_digit(self):
        self.assertTrue(is_number("1"))

    def test_large_number(self):
        self.assertTrue(is_number("999999999"))

    def test_negative_float(self):
        self.assertTrue(is_number("-0.001"))


class TestMakeKey(unittest.TestCase):
    def test_basic(self):
        self.assertEqual(make_key(0, 0), "0:0")

    def test_positive_indices(self):
        self.assertEqual(make_key(3, 7), "3:7")

    def test_large_indices(self):
        self.assertEqual(make_key(100, 200), "100:200")

    def test_string_inputs(self):
        # Lua's key() calls tostring on both – ensure equivalent behaviour
        self.assertEqual(make_key("5", "9"), "5:9")

    def test_negative_indices(self):
        self.assertEqual(make_key(-1, -2), "-1:-2")

    def test_zero_and_nonzero(self):
        self.assertEqual(make_key(0, 15), "0:15")

    def test_uniqueness(self):
        # Distinct (ix,iz) pairs must produce distinct keys
        self.assertNotEqual(make_key(1, 2), make_key(2, 1))
        self.assertNotEqual(make_key(1, 2), make_key(1, 3))


class TestClusterSorted(unittest.TestCase):
    def test_empty_list(self):
        self.assertEqual(cluster_sorted([], 1.0), [])

    def test_single_element(self):
        result = cluster_sorted([5.0], 1.0)
        self.assertEqual(len(result), 1)
        self.assertAlmostEqual(result[0], 5.0)

    def test_all_identical(self):
        result = cluster_sorted([3.0, 3.0, 3.0], 0.5)
        self.assertEqual(len(result), 1)
        self.assertAlmostEqual(result[0], 3.0)

    def test_two_distinct_clusters(self):
        result = cluster_sorted([1.0, 1.1, 5.0, 5.1], 0.5)
        self.assertEqual(len(result), 2)
        self.assertAlmostEqual(result[0], 1.05, places=5)
        self.assertAlmostEqual(result[1], 5.05, places=5)

    def test_all_separate(self):
        result = cluster_sorted([1.0, 3.0, 5.0], 0.5)
        self.assertEqual(len(result), 3)
        self.assertAlmostEqual(result[0], 1.0)
        self.assertAlmostEqual(result[1], 3.0)
        self.assertAlmostEqual(result[2], 5.0)

    def test_epsilon_boundary_not_merged(self):
        # Points exactly at epsilon+1 apart should NOT merge
        result = cluster_sorted([0.0, 2.0], 1.0)  # diff=2, epsilon=1 → separate
        self.assertEqual(len(result), 2)

    def test_epsilon_boundary_merged(self):
        # Points within epsilon should merge
        result = cluster_sorted([0.0, 1.0], 1.0)  # diff=1 ≤ epsilon=1 → merged
        self.assertEqual(len(result), 1)
        self.assertAlmostEqual(result[0], 0.5)

    def test_running_average_update(self):
        # Three points in one cluster – centre is running average
        result = cluster_sorted([0.0, 1.0, 2.0], 2.0)
        self.assertEqual(len(result), 1)
        # Running average: start=0, then +(1-0)/2=0.5, then +(2-0.5)/3=1.0
        self.assertAlmostEqual(result[0], 1.0, places=9)

    def test_grid_spacing_typical(self):
        # Simulate a 5-cell grid at spacing 4, with ε=2.4
        positions = [0.0, 4.0, 8.0, 12.0, 16.0]
        result = cluster_sorted(positions, 2.4)
        self.assertEqual(len(result), 5)

    def test_large_epsilon_collapses_all(self):
        result = cluster_sorted([1.0, 2.0, 3.0, 4.0], 10.0)
        self.assertEqual(len(result), 1)


class TestMedianLua(unittest.TestCase):
    def test_empty_returns_none(self):
        self.assertIsNone(median_lua([]))

    def test_single_element(self):
        self.assertEqual(median_lua([7.0]), 7.0)

    def test_odd_length(self):
        self.assertEqual(median_lua([3.0, 1.0, 2.0]), 2.0)

    def test_even_length_lower_median(self):
        # floor((4+1)/2) = 2 → index 1 (0-based) → 2nd smallest
        result = median_lua([4.0, 1.0, 3.0, 2.0])
        self.assertEqual(result, 2.0)

    def test_already_sorted(self):
        self.assertEqual(median_lua([1.0, 2.0, 3.0, 4.0, 5.0]), 3.0)

    def test_duplicate_values(self):
        self.assertEqual(median_lua([2.0, 2.0, 2.0]), 2.0)

    def test_two_elements_lower(self):
        # floor((2+1)/2) = 1 → returns 1st element
        result = median_lua([10.0, 20.0])
        self.assertEqual(result, 10.0)

    def test_negative_values(self):
        self.assertEqual(median_lua([-3.0, -1.0, -2.0]), -2.0)

    def test_single_zero(self):
        self.assertEqual(median_lua([0.0]), 0.0)


class TestTypicalSpacing(unittest.TestCase):
    def test_empty_returns_4(self):
        self.assertEqual(typical_spacing([]), 4.0)

    def test_single_element_returns_4(self):
        self.assertEqual(typical_spacing([5.0]), 4.0)

    def test_two_elements(self):
        self.assertEqual(typical_spacing([0.0, 4.0]), 4.0)

    def test_uniform_spacing(self):
        centers = [0.0, 4.0, 8.0, 12.0, 16.0]
        self.assertEqual(typical_spacing(centers), 4.0)

    def test_varied_spacing_median(self):
        # diffs: [1, 1, 1, 10] → sorted [1,1,1,10] → median at index 2 → 1
        centers = [0.0, 1.0, 2.0, 3.0, 13.0]
        self.assertEqual(typical_spacing(centers), 1.0)

    def test_single_diff(self):
        self.assertEqual(typical_spacing([0.0, 7.0]), 7.0)

    def test_non_uniform_large_median(self):
        # diffs [2, 2, 2, 100] → median at floor(5/2)=2 → 2
        centers = [0.0, 2.0, 4.0, 6.0, 106.0]
        self.assertEqual(typical_spacing(centers), 2.0)


class TestNearestIndex(unittest.TestCase):
    def test_empty_returns_minus1(self):
        self.assertEqual(nearest_index(5.0, []), -1)

    def test_exact_first_element(self):
        self.assertEqual(nearest_index(1.0, [1.0, 2.0, 3.0]), 0)

    def test_exact_last_element(self):
        self.assertEqual(nearest_index(3.0, [1.0, 2.0, 3.0]), 2)

    def test_exact_middle_element(self):
        self.assertEqual(nearest_index(2.0, [1.0, 2.0, 3.0]), 1)

    def test_nearest_to_left(self):
        self.assertEqual(nearest_index(1.4, [1.0, 2.0, 3.0]), 0)

    def test_nearest_to_right(self):
        self.assertEqual(nearest_index(1.6, [1.0, 2.0, 3.0]), 1)

    def test_single_element(self):
        self.assertEqual(nearest_index(99.0, [5.0]), 0)

    def test_value_before_all_centers(self):
        # v is less than all centers → nearest is first (index 0)
        self.assertEqual(nearest_index(-10.0, [1.0, 2.0, 3.0]), 0)

    def test_value_after_all_centers(self):
        # v is greater than all centers → nearest is last
        self.assertEqual(nearest_index(100.0, [1.0, 2.0, 3.0]), 2)

    def test_two_element_midpoint_left(self):
        # midpoint = 1.5; v=1.2 is closer to 1.0 (index 0)
        self.assertEqual(nearest_index(1.2, [1.0, 2.0]), 0)

    def test_two_element_midpoint_right(self):
        # v=1.8 is closer to 2.0 (index 1)
        self.assertEqual(nearest_index(1.8, [1.0, 2.0]), 1)

    def test_returns_zero_based_index(self):
        # Verifies return is 0-based
        centers = [10.0, 20.0, 30.0, 40.0]
        self.assertEqual(nearest_index(10.0, centers), 0)
        self.assertEqual(nearest_index(40.0, centers), 3)

    def test_large_grid(self):
        centers = [float(i * 4) for i in range(20)]
        # Exact match at index 10 → value 40.0
        self.assertEqual(nearest_index(40.0, centers), 10)


class TestIsCoveredCell(unittest.TestCase):
    def test_none_returns_false(self):
        self.assertFalse(is_covered_cell(None))

    def test_state_number_returns_false(self):
        cell = {"state": "number", "covered": True}
        self.assertFalse(is_covered_cell(cell))

    def test_covered_true(self):
        cell = {"state": "unknown", "covered": True}
        self.assertTrue(is_covered_cell(cell))

    def test_covered_none_is_truthy(self):
        # covered ~= false → True when covered is None (not set)
        cell = {"state": "unknown"}
        self.assertTrue(is_covered_cell(cell))

    def test_covered_false_returns_false(self):
        cell = {"state": "unknown", "covered": False}
        self.assertFalse(is_covered_cell(cell))

    def test_missing_state_key(self):
        # No "state" key → get() returns None, not "number" → covered check applies
        cell = {"covered": True}
        self.assertTrue(is_covered_cell(cell))

    def test_state_unknown_covered_false(self):
        cell = {"state": "unknown", "covered": False}
        self.assertFalse(is_covered_cell(cell))

    def test_state_number_covered_false(self):
        # state=="number" short-circuits; covered value doesn't matter
        cell = {"state": "number", "covered": False}
        self.assertFalse(is_covered_cell(cell))

    def test_state_number_covered_true(self):
        cell = {"state": "number", "covered": True}
        self.assertFalse(is_covered_cell(cell))


class TestNChooseK(unittest.TestCase):
    def test_zero_k(self):
        self.assertEqual(n_choose_k(5, 0), 1)

    def test_k_equals_n(self):
        self.assertEqual(n_choose_k(5, 5), 1)

    def test_k_greater_than_n_returns_0(self):
        self.assertEqual(n_choose_k(3, 5), 0)

    def test_negative_k_returns_0(self):
        self.assertEqual(n_choose_k(5, -1), 0)

    def test_choose_1(self):
        self.assertEqual(n_choose_k(7, 1), 7)

    def test_choose_2(self):
        self.assertEqual(n_choose_k(5, 2), 10)

    def test_choose_3(self):
        self.assertEqual(n_choose_k(6, 3), 20)

    def test_symmetry(self):
        # C(n,k) == C(n,n-k)
        self.assertAlmostEqual(n_choose_k(10, 3), n_choose_k(10, 7))

    def test_n_0_k_0(self):
        self.assertEqual(n_choose_k(0, 0), 1)

    def test_large_values(self):
        # C(20, 10) = 184756
        self.assertAlmostEqual(n_choose_k(20, 10), 184756.0, places=0)

    def test_pascal_identity(self):
        # C(n,k) == C(n-1,k-1) + C(n-1,k)
        for n in range(1, 10):
            for k in range(1, n):
                self.assertAlmostEqual(
                    n_choose_k(n, k),
                    n_choose_k(n - 1, k - 1) + n_choose_k(n - 1, k),
                    places=6,
                )

    def test_boundary_n1(self):
        self.assertEqual(n_choose_k(1, 0), 1)
        self.assertEqual(n_choose_k(1, 1), 1)


class TestMakeBitmaskSet(unittest.TestCase):
    def test_empty_membership_lists(self):
        result = make_bitmasks_set([])
        self.assertEqual(result, [])

    def test_single_list_single_element(self):
        result = make_bitmasks_set([[1]])
        self.assertEqual(result, [{1: True}])

    def test_single_list_multiple_elements(self):
        result = make_bitmasks_set([[1, 2, 3]])
        self.assertEqual(result, [{1: True, 2: True, 3: True}])

    def test_multiple_lists(self):
        result = make_bitmasks_set([[1, 2], [2, 3], [4]])
        self.assertEqual(len(result), 3)
        self.assertEqual(result[0], {1: True, 2: True})
        self.assertEqual(result[1], {2: True, 3: True})
        self.assertEqual(result[2], {4: True})

    def test_overlapping_lists(self):
        result = make_bitmasks_set([[1, 2, 3], [3, 4, 5]])
        self.assertIn(3, result[0])
        self.assertIn(3, result[1])


class TestIsSubsetMaskSet(unittest.TestCase):
    def test_empty_is_subset_of_anything(self):
        self.assertTrue(is_subset_mask_set({}, {1: True, 2: True}))

    def test_equal_sets_are_subsets(self):
        s = {1: True, 2: True}
        self.assertTrue(is_subset_mask_set(s, s))

    def test_proper_subset(self):
        A = {1: True}
        B = {1: True, 2: True, 3: True}
        self.assertTrue(is_subset_mask_set(A, B))

    def test_not_subset(self):
        A = {1: True, 4: True}
        B = {1: True, 2: True, 3: True}
        self.assertFalse(is_subset_mask_set(A, B))

    def test_disjoint_sets(self):
        A = {1: True}
        B = {2: True}
        self.assertFalse(is_subset_mask_set(A, B))

    def test_larger_is_not_subset_of_smaller(self):
        A = {1: True, 2: True, 3: True}
        B = {1: True, 2: True}
        self.assertFalse(is_subset_mask_set(A, B))


class TestDiffMaskSet(unittest.TestCase):
    def test_empty_A_and_B(self):
        self.assertEqual(diff_mask_set({}, {}), [])

    def test_empty_A_returns_all_of_B(self):
        B = {1: True, 2: True, 3: True}
        result = diff_mask_set({}, B)
        self.assertEqual(sorted(result), [1, 2, 3])

    def test_equal_sets_returns_empty(self):
        s = {1: True, 2: True}
        self.assertEqual(diff_mask_set(s, s), [])

    def test_B_minus_A(self):
        A = {1: True, 2: True}
        B = {1: True, 2: True, 3: True, 4: True}
        result = sorted(diff_mask_set(A, B))
        self.assertEqual(result, [3, 4])

    def test_disjoint(self):
        A = {1: True, 2: True}
        B = {3: True, 4: True}
        result = sorted(diff_mask_set(A, B))
        self.assertEqual(result, [3, 4])

    def test_A_superset_of_B(self):
        A = {1: True, 2: True, 3: True, 4: True}
        B = {1: True, 2: True}
        self.assertEqual(diff_mask_set(A, B), [])


class TestConstraintKey(unittest.TestCase):
    def test_single_constraint(self):
        constraints = [{"idxs": [3, 1, 2], "rem": 1}]
        result = constraint_key(constraints)
        self.assertEqual(result, "1,2,3:1")

    def test_multiple_constraints_sorted(self):
        constraints = [
            {"idxs": [3, 1], "rem": 2},
            {"idxs": [2, 4], "rem": 0},
        ]
        result = constraint_key(constraints)
        # "1,3:2" and "2,4:0" → sorted → "1,3:2|2,4:0"
        self.assertEqual(result, "1,3:2|2,4:0")

    def test_same_constraints_different_order_produce_same_key(self):
        c1 = [{"idxs": [1, 2], "rem": 1}, {"idxs": [3, 4], "rem": 2}]
        c2 = [{"idxs": [3, 4], "rem": 2}, {"idxs": [1, 2], "rem": 1}]
        self.assertEqual(constraint_key(c1), constraint_key(c2))

    def test_empty_constraints(self):
        self.assertEqual(constraint_key([]), "")

    def test_idxs_sorted_within_constraint(self):
        constraints = [{"idxs": [5, 3, 1], "rem": 3}]
        result = constraint_key(constraints)
        self.assertEqual(result, "1,3,5:3")

    def test_rem_zero(self):
        constraints = [{"idxs": [2, 1], "rem": 0}]
        self.assertEqual(constraint_key(constraints), "1,2:0")

    def test_key_separates_rem_correctly(self):
        # Ensure "rem" is correctly appended after ":"
        constraints = [{"idxs": [1], "rem": 5}]
        self.assertEqual(constraint_key(constraints), "1:5")


class TestFmtPct(unittest.TestCase):
    def test_zero(self):
        self.assertEqual(fmt_pct(0.0), "0%")

    def test_one(self):
        self.assertEqual(fmt_pct(1.0), "100%")

    def test_half(self):
        self.assertEqual(fmt_pct(0.5), "50%")

    def test_rounds_to_nearest_5(self):
        # 0.73 → floor(0.73*20+0.5)/20 = floor(15.1)/20 = 15/20 = 0.75 → 75%
        self.assertEqual(fmt_pct(0.73), "75%")

    def test_rounds_down(self):
        # 0.71 → floor(0.71*20+0.5)/20 = floor(14.7)/20 = 14/20 = 0.70 → 70%
        self.assertEqual(fmt_pct(0.71), "70%")

    def test_quarter(self):
        self.assertEqual(fmt_pct(0.25), "25%")

    def test_three_quarters(self):
        self.assertEqual(fmt_pct(0.75), "75%")

    def test_small_value(self):
        # 0.01 → floor(0.01*20+0.5)/20 = floor(0.7)/20 = 0/20 = 0.0 → 0%
        self.assertEqual(fmt_pct(0.01), "0%")

    def test_large_threshold(self):
        # 0.95 → floor(19.5)/20 = 19/20 = 0.95 → 95%
        self.assertEqual(fmt_pct(0.95), "95%")

    def test_0_05(self):
        # 0.05 → floor(1.5)/20 = 1/20 = 0.05 → 5%
        self.assertEqual(fmt_pct(0.05), "5%")


class TestComputePartsSig(unittest.TestCase):
    def _pos(self, x: float, z: float) -> Dict:
        return {"Position": {"X": x, "Z": z}}

    def test_empty_parts_returns_zero(self):
        self.assertEqual(compute_parts_signature([]), "0")

    def test_single_part(self):
        parts = [self._pos(1.0, 2.0)]
        result = compute_parts_signature(parts)
        # n=1, step=max(1,floor(1/12))=1; acc=[1], then i=0, pos→X=10,Z=20
        self.assertEqual(result, "1|10,20")

    def test_two_parts(self):
        parts = [self._pos(1.0, 2.0), self._pos(3.0, 4.0)]
        result = compute_parts_signature(parts)
        self.assertIn("2", result)

    def test_quantises_position(self):
        # X=1.05 → floor(1.05*10+0.5)=floor(11.0)=11
        parts = [self._pos(1.05, 0.0)]
        result = compute_parts_signature(parts)
        self.assertIn("11,0", result)

    def test_samples_at_most_12_parts(self):
        # 24 parts, step=max(1,floor(24/12))=2 → samples indices 0,2,4,...22
        parts = [self._pos(float(i), 0.0) for i in range(24)]
        result = compute_parts_signature(parts)
        # Count commas in position tokens (each position is "x,z")
        tokens = result.split("|")
        # First token is count "24"; rest are positions; at most 12 positions
        self.assertLessEqual(len(tokens) - 1, 12)
        self.assertEqual(tokens[0], "24")

    def test_includes_count_first(self):
        parts = [self._pos(0.0, 0.0), self._pos(5.0, 5.0)]
        result = compute_parts_signature(parts)
        self.assertTrue(result.startswith("2|"))

    def test_rounding_negative_positions(self):
        # X=-0.05 → floor(-0.05*10+0.5)=floor(0.0)=0
        parts = [self._pos(-0.05, 0.0)]
        result = compute_parts_signature(parts)
        self.assertIn("0,0", result)

    def test_part_without_position_is_skipped(self):
        # A part without "Position" key should not contribute a position token
        parts = [{}]  # no Position
        result = compute_parts_signature(parts)
        # Still starts with count "1", no position token appended
        self.assertEqual(result, "1")


class TestEnumerateComponent(unittest.TestCase):
    """
    Tests for the backtracking constraint-satisfaction solver.

    Cell indices in constraints are 1-based (matching Lua convention).
    """

    def test_no_constraints_two_cells(self):
        # No constraints → every assignment valid → 2^2 = 4 solutions
        comp_cells = ["A", "B"]
        constraints = []
        total, counts, min_m, max_m, pmf, _, capped = enumerate_component(
            comp_cells, constraints, None
        )
        self.assertEqual(total, 4)
        self.assertFalse(capped)

    def test_exactly_one_mine_in_two_cells(self):
        # One constraint: exactly 1 mine among cells 1 and 2
        comp_cells = ["A", "B"]
        constraints = [{"idxs": [1, 2], "rem": 1}]
        total, counts, min_m, max_m, pmf, _, capped = enumerate_component(
            comp_cells, constraints, None
        )
        self.assertEqual(total, 2)  # {A=1,B=0} or {A=0,B=1}
        self.assertEqual(counts[0], 1)  # cell A is mine in 1 of 2 solutions
        self.assertEqual(counts[1], 1)  # cell B is mine in 1 of 2 solutions
        self.assertEqual(min_m, 1)
        self.assertEqual(max_m, 1)
        self.assertFalse(capped)

    def test_exactly_zero_mines(self):
        # rem=0 → all cells must be safe
        comp_cells = ["A", "B", "C"]
        constraints = [{"idxs": [1, 2, 3], "rem": 0}]
        total, counts, min_m, max_m, pmf, _, capped = enumerate_component(
            comp_cells, constraints, None
        )
        self.assertEqual(total, 1)
        self.assertEqual(counts, [0, 0, 0])
        self.assertEqual(min_m, 0)
        self.assertEqual(max_m, 0)

    def test_all_mines(self):
        # rem==n → all cells must be mines
        comp_cells = ["A", "B", "C"]
        constraints = [{"idxs": [1, 2, 3], "rem": 3}]
        total, counts, min_m, max_m, pmf, _, capped = enumerate_component(
            comp_cells, constraints, None
        )
        self.assertEqual(total, 1)
        self.assertEqual(counts, [1, 1, 1])
        self.assertEqual(min_m, 3)
        self.assertEqual(max_m, 3)

    def test_solution_cap_triggers_capped(self):
        # 4 cells, no constraints → 16 solutions; cap at 4 → capped=True
        comp_cells = ["A", "B", "C", "D"]
        constraints = []
        total, counts, min_m, max_m, pmf, _, capped = enumerate_component(
            comp_cells, constraints, 4
        )
        self.assertTrue(capped)
        self.assertLessEqual(total, 4)

    def test_pmf_entries_exist_for_all_mine_counts(self):
        comp_cells = ["A", "B"]
        constraints = [{"idxs": [1, 2], "rem": 1}]
        total, counts, min_m, max_m, pmf, _, _ = enumerate_component(
            comp_cells, constraints, None
        )
        # pmf should have entries for 0..n
        self.assertIn(0, pmf)
        self.assertIn(1, pmf)
        self.assertIn(2, pmf)

    def test_pmf_sums_to_total(self):
        comp_cells = ["A", "B", "C"]
        constraints = [{"idxs": [1, 2, 3], "rem": 1}]
        total, counts, min_m, max_m, pmf, _, _ = enumerate_component(
            comp_cells, constraints, None
        )
        self.assertEqual(sum(pmf.values()), total)

    def test_counts_per_var_sum_matches_total_mines_times_total(self):
        # For 1-mine-in-3 constraint: total=3, each cell appears in 1 solution
        comp_cells = ["A", "B", "C"]
        constraints = [{"idxs": [1, 2, 3], "rem": 1}]
        total, counts, _, _, _, _, _ = enumerate_component(
            comp_cells, constraints, None
        )
        self.assertEqual(total, 3)
        self.assertEqual(counts[0], 1)
        self.assertEqual(counts[1], 1)
        self.assertEqual(counts[2], 1)

    def test_two_overlapping_constraints(self):
        # Cells 1,2,3: C1={1,2}=1 mine, C2={2,3}=1 mine
        # Valid assignments:
        #   1=1,2=0,3=1 → C1: assigned=1 ✓, C2: assigned=1 ✓
        #   1=0,2=1,3=0 → C1: assigned=1 ✓, C2: assigned=1 ✓
        comp_cells = ["A", "B", "C"]
        constraints = [
            {"idxs": [1, 2], "rem": 1},
            {"idxs": [2, 3], "rem": 1},
        ]
        total, counts, min_m, max_m, pmf, _, capped = enumerate_component(
            comp_cells, constraints, None
        )
        self.assertEqual(total, 2)
        self.assertFalse(capped)
        # Cell B (index 1, 0-based) appears as mine in exactly 1 solution
        self.assertEqual(counts[1], 1)

    def test_infeasible_constraints(self):
        # rem=1 but only 1 cell; also rem=0 on same cell → infeasible
        comp_cells = ["A"]
        constraints = [
            {"idxs": [1], "rem": 1},
            {"idxs": [1], "rem": 0},
        ]
        total, counts, min_m, max_m, pmf, _, _ = enumerate_component(
            comp_cells, constraints, None
        )
        self.assertEqual(total, 0)

    def test_counts_per_var_per_k_correct(self):
        # 1 mine among 2 cells; in both solutions 1 mine total → k=1
        comp_cells = ["A", "B"]
        constraints = [{"idxs": [1, 2], "rem": 1}]
        total, counts, _, _, pmf, cpvk, _ = enumerate_component(
            comp_cells, constraints, None
        )
        # Cell A is a mine in 1 solution with k=1
        self.assertEqual(cpvk[0].get(1, 0), 1)
        # Cell B is a mine in 1 solution with k=1
        self.assertEqual(cpvk[1].get(1, 0), 1)

    def test_no_constraint_single_cell(self):
        # 1 cell, no constraints → 2 solutions: mine or safe
        comp_cells = ["A"]
        constraints = []
        total, counts, _, _, pmf, _, _ = enumerate_component(
            comp_cells, constraints, None
        )
        self.assertEqual(total, 2)
        self.assertEqual(counts[0], 1)  # mine in 1 of 2 solutions


if __name__ == "__main__":
    unittest.main()
