# -*- coding: utf-8 -*-
"""Cooperative asymptotically non-vanishing (ANV) bandit experiments. Open in Spyder and press F5 to run. Requires numpy, numba and matplotlib."""

# %% ======================= User configuration starts here =======================
# Common settings are (1) the number of agents, arms, rounds and replicates, (2) the algorithms to compare, and (3) shared parameters for window-based algorithms.
# Set the output location in section 7 (OUTPUT). This Spyder cell can be run independently.
CONFIG = {
    # --- 1. Shared experimental settings -------------------------------------------
    "RUN": True,                 # Press F5 to run the experiments, or call main(CONFIG) after importing the module.
    "QUICK_CHECK": False,        # If True, use at most 4 agents, 8 arms and 300 rounds, with 3 replicates per scenario.
    "SELF_CHECK": True,          # Run numerical self-checks before the experiments.
    "N_AGENTS": 25,              # Number of agents n in the base instance
    "N_ARMS": 100,               # Number of arms K in the base instance
    "HORIZON": 300000,           # Rounds T per agent. Each algorithm has the same team pull budget nT within a scenario.
    "SEED": 20261013,            # Master seed. Algorithms share the underlying reward draws within each scenario and replicate.
    "RUN_LAMBDA_0": True,        # Individual decay depends on the agent's own pull count.
    "RUN_LAMBDA_1": True,        # Shared decay depends on team pull counts at the start of the round.
    # Change 50 below to set the number of replicates for all groups.
    "REPEATS": dict.fromkeys(("MAIN", "SMALL_GAP", "PLATEAU", "STAR", "RANDOM_PER_INSTANCE"), 50),

    # --- 2. Algorithms to compare (True to include, False to skip) ------------------
    "ALGORITHMS": {
        "bgosine": True,         # B-GosInE runs UCB on the active set and recommends the most-played arm in each phase.
        "full_ucb": True,        # Independent UCB over all arms
        "eff_fewa": True,        # Independent EFF-FEWA over all arms
        "no_comm": True,         # No recommendations. UCB uses only the initial active set.
        "random_rec": True,      # Random recommendations with the same budget. Sample uniformly from the sender's active set.
        "coop_eff_fewa": True,   # Cooperative EFF-FEWA uses the recommendation and replacement rules of B-GosInE.
        "eff_raw_ucb": True,     # Independent EFF-RAW-UCB over all arms
        "fewa": False,           # FEWA with all integer window sizes. For short horizons only (see EXACT_FEWA_MAX_T).
        "central_fewa": True,    # Centralized batch baseline for shared decay. All agents pull the same arm each round and pool rewards.
    },

    # --- 3. Shared and algorithm-specific parameters ------------------------------
    # If True, all window-based algorithms use ALPHA, DELTA0, INCLUDE_K and SIGMA2 from WINDOW.
    # Edit WINDOW once to change these defaults, or set False to enable algorithm-specific values.
    "UNIFY_WINDOW_PARAMS": True,
    "WINDOW": {
        "ALPHA": 2,           # Exponent in the confidence parameter delta_t = DELTA0 / t**ALPHA
        "DELTA0": 1.0,           # Initial confidence parameter
        "INCLUDE_K": False,      # If True, divide delta_t by K as well.
        "SIGMA2": 0.25,          # Variance proxy for a Bernoulli reward. The centralized kernel divides it by n for batch means.
        "CENTRAL_ENGINE": "eff_fewa",  # Centralized algorithm, either "eff_fewa" or "fewa"
        # Optional centralized overrides. None uses the corresponding shared value.
        "CENTRAL_ALPHA": None,
        "CENTRAL_DELTA0": None,
        "CENTRAL_INCLUDE_K": None,
        "CENTRAL_SIGMA2": None,
        "EXACT_FEWA_MAX_T": 5000,      # Maximum horizon for FEWA with all integer window sizes
        "MAX_MEMORY_MB_PER_RUN": 1024, # Memory budget (MB) for window statistics per trajectory
    },
    "RAW_UCB": {
        "ALPHA": 1.4,            # Used only when UNIFY_WINDOW_PARAMS=False. The default uses WINDOW.ALPHA.
        "DELTA0": None, "INCLUDE_K": None, "SIGMA2": None,  # Inherit from WINDOW
    },
    # Both efficient window methods use window sizes 1, 2, 4, and so on. For standard UCB methods, DELTA below sets the confidence radius.
    "COMMUNICATION": {
        "NETWORK": "complete",   # Base network: "complete", "ring", "star" or "custom"
        "CUSTOM_P": None,        # n-by-n contact probability matrix for a custom network
        "STAR_CENTER": 0,        # Zero-based index of the center of the star graph
        "H": 1,                  # Interval h between communication opportunities
        "SCHEDULE": "scaled",    # "scaled" uses the confidence term. "fixed" uses FIXED_H.
        "XI": 1.0,               # Phase scale factor xi for the scaled schedule
        "FIXED_H": 10,           # Phase scale for the fixed schedule. Must be an integer multiple of h.
        "BETA": 2.0,             # Phase end time H * ceil(phase index ** BETA)
        "DELTA": None,           # None uses (T+1)^(-2) for the UCB confidence radius and the scaled communication schedule.
    },

    # --- 4. Shared reward environment (parameter sweeps can override these base settings) ---
    "INSTANCE": {
        "FAMILY": "exp",         # Options: "stationary", "exp", "power", "plateau"
        "BASE_BEST": 0.6,        # Limiting mean reward of the optimal arm
        "GAP": 0.1,              # Gap in limiting mean reward between the optimal and suboptimal arms in fixed instances
        "BEST_ARM": None,        # None selects automatically. Use one-based indexing to specify the arm manually.
        "AMPLITUDE": 0.2,        # Base decay amplitude
        "EXP_RATE": 0.01,        # Base exponential decay rate
        "POWER_EXPONENT": 0.5,   # Power-law decay exponent, separate from the window confidence exponent ALPHA
        "PLATEAU_LENGTH": 10000,
        "HETEROGENEOUS": True,   # Use arm-specific multipliers for decay rates or plateau lengths.
        "RATE_MULTIPLIER_RANGE": [0.75, 1.25],
        "ALLOW_MIXED_FAMILIES": False,
        "MIXED_FAMILIES": ["exp", "power", "plateau"],
        "RANDOM_GAP_RANGE": [0.05, 0.2],
        "EARLY_LATE_CONFLICT": True,  # Give some arms that are suboptimal in the long run a higher initial mean reward.
        "CONFLICT_FRACTION": 0.2,     # Probability of selecting each eligible suboptimal arm
        "INITIAL_ADVANTAGE": 0.05,    # Initial reward advantage of selected arms over the long-run optimal arm
        "BEST_AMPLITUDE": 0.05,       # Decay amplitude of the long-run optimal arm in instances with a ranking reversal
        # For base or random instances, specify values per arm or use None to apply the rules above.
        "MANUAL": {"bases": None, "amplitudes": None, "rates": None,
                   "plateau_lengths": None, "families": None},
    },

    # --- 5. Experiments (select candidate groups first, then the comparison plots) ---
    "EXPERIMENTS": {
        "RATE_REGRET": True,     # Decay group: compare regret across exponential decay rates.
        "NETWORK_REGRET": False, # Network group: also compute regret and optimal-arm availability and selection curves.
    },
    "GROUPS": {
        "basic": True, "small_gap": True, "plateau": True,  # Base case, small gap and two-arm plateau stress test
        "decay": True, "network": True, "schedule": True,   # Decay, network topology and communication schedule
        "scale": True, "public_bias": True, "random_instances": True,
    },
    # Only trajectories required by selected plots are simulated. Enabling a group runs the settings needed for those plots.
    "SCANS": {
        "GAPS": [0.025, 0.05, 0.1, 0.2, 0.3],
        "EXP_RATES": [0.001, 0.01, 0.1],
        "POWER_EXPONENTS": [0.25, 0.5, 1.0, 2.0],
        "PLATEAU_LENGTHS": [2000, 10000, 50000, 200000],
        "PLATEAU_T_RATIO": 1.5, "FIXED_PLATEAU_L": 10000,
        "PLATEAU_HORIZONS": [15000, 30000, 100000, 300000],
        "NETWORKS": ["complete", "ring", "star"], "STAR_STARTS": ["center", "leaf"],
        "XI": [0.1, 1.0, 10.0, 100.0], "INCLUDE_H_EQUALS_h": True,
        "H": [1, 10, 100, 1000], "SCHEDULE_GAPS": [0.05],
        "AGENTS": [4, 8, 16, 32], "ARMS": [32, 64, 128], "ARMS_PER_AGENT": 4,
        "PUBLIC_BIAS_AGENTS": [4, 16, 32], "PUBLIC_BIAS_POWER": 0.5,
        "RANDOM_INSTANCES": 5,
    },

    # --- 6. Evaluation and execution ----------------------------------------------
    "ORACLE": {
        "PUBLIC_MODE": "auto",  # Oracle benchmark under shared decay. Options: "auto", "exact", "bounds".
        "MAX_STATES": 100000, "MAX_TRANSITIONS": 2000000, "MAX_SECONDS": 20.0,
    },
    "EXECUTION": {
        "WORKERS": "auto",      # Use a short benchmark to select the number of threads, or specify a positive integer.
        "MAX_HOURS": None,      # None runs all tasks. At the time limit, summarize completed pairs.
        "CHECKPOINTS": 501, "LOG_CHECKPOINTS": 100,
        "RECENT_WINDOW": 10000, # Window for computing the recent optimal-arm selection frequency
        "PROGRESS_EVERY": 50,   # Report progress after this many completed tasks.
    },

    # --- 7. Output location and figures -------------------------------------------
    "OUTPUT": {
        "DIRECTORY": None,      # None writes to anv_results in the script directory.
        "SAVE_PLOTS": True, "SHOW_PLOTS": False,
        "SAVE_ENDPOINT_CSV": True,  # Per-seed endpoints and paired differences relative to B-GosInE
        "ONLY_BGOSINE_PLOTS": False,
        "EXTRA_BASIC_PLOTS": [
            "03_team_cumulative_pseudo_regret", "05_limiting_mean_loss", "07_recommendation_accuracy",
            "10_cumulative_expected_reward", "12_selection_loss_when_optimal_arm_available", "14_message_count_and_payload_bits",
        ],
        "DPI": 170, "FONT_PATH": None,  # None selects an available system font automatically.
    },
}
# ========================= End of user configuration =========================

# %% Algorithm implementations and experiment runner
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from datetime import datetime
import copy
import csv
import hashlib
import json
import math
import os
import time
import warnings

try:
    import numpy as np
    from numba import njit
except ImportError as exc:
    raise ImportError("In the current Spyder environment, run %pip install numpy numba matplotlib and restart the kernel.") from exc

VERSION = "2026.11.20.extended.2"

FAMILY_IDS = {"stationary": 0, "exp": 1, "power": 2, "plateau": 3}



ALGORITHM_IDS = {"bgosine": 0, "full_ucb": 1, "no_comm": 2,
                 "eff_fewa": 3, "fewa": 4, "central_fewa": 5,
                 "coop_eff_fewa": 7, "eff_raw_ucb": 8, "random_rec": 9}



_REPORT_LABELS = {
    "bgosine": "B-GosInE (cooperative)",
    "full_ucb": "Independent UCB (all arms)",
    "independent_fewa": "Independent EFF-FEWA (empirical parameters)",
    "eff_fewa": "Independent EFF-FEWA (empirical parameters)",
    "fewa": "Independent FEWA",
    "no_comm": "No recommendations (fixed initial set)",
    "random_rec": "Random recommendations (active-set UCB)",
    "coop_eff_fewa": "Cooperative EFF-FEWA",
    "eff_raw_ucb": "Independent EFF-RAW-UCB",
    "single_dcto": "Single-agent D-CTO",
    "single_ucb": "Single-agent UCB (all arms)",
    "central_fewa": "Centralized batched EFF-FEWA (empirical parameters)",
    "centralized_fewa": "Centralized batched EFF-FEWA (empirical parameters)",
}



@njit(cache=False, nogil=True)
def curve_mean(kind, b, a, p, length, q):
    """q starts at 1. Under shared decay, all agents use the same start-of-round q for a given arm."""
    if kind == 0:
        return b
    if kind == 1:
        return b + a * math.exp(-p * (q - 1.0))
    if kind == 2:
        return b + a * q ** (-p)
    return b + (a if q <= length else 0.0)



@njit(cache=False, nogil=True)
def _oracle_sift_down(heap, values, pos):
    """Maintain a max-heap, breaking ties in mean reward in favor of the smaller arm index."""
    size = heap.size
    item = heap[pos]
    while 2 * pos + 1 < size:
        child = 2 * pos + 1
        if child + 1 < size:
            left, right = heap[child], heap[child + 1]
            if values[right] > values[left] or (
                    values[right] == values[left] and right < left):
                child += 1
        candidate = heap[child]
        if values[item] > values[candidate] or (
                values[item] == values[candidate] and item < candidate):
            break
        heap[pos] = candidate
        pos = child
    heap[pos] = item



@njit(cache=False, nogil=True)
def _oracle_greedy_prefix(bases, amps, rates, lengths, kinds,
                          checkpoints, count_step, reward_factor):
    """Merge nonincreasing marginal rewards in O(last checkpoint * log K) time and O(K + number of checkpoints) space."""
    size = bases.size
    values = np.empty(size)
    counts = np.zeros(size, dtype=np.int64)
    heap = np.arange(size)
    for k in range(size):
        values[k] = curve_mean(kinds[k], bases[k], amps[k], rates[k], lengths[k], 1)
    for pos in range(size // 2 - 1, -1, -1):
        _oracle_sift_down(heap, values, pos)
    result = np.zeros(checkpoints.size)
    cp, total, correction = 1, 0.0, 0.0
    for step in range(1, checkpoints[-1] + 1):
        chosen = heap[0]
        # Use Kahan summation to prevent roundoff over millions of steps from appearing as negative regret.
        increment = reward_factor * values[chosen] - correction
        updated = total + increment
        correction = (updated - total) - increment
        total = updated
        counts[chosen] += count_step
        values[chosen] = curve_mean(kinds[chosen], bases[chosen], amps[chosen],
                                    rates[chosen], lengths[chosen], counts[chosen] + 1)
        _oracle_sift_down(heap, values, 0)
        if cp < checkpoints.size and step == checkpoints[cp]:
            result[cp] = total
            cp += 1
    return result



class OracleBudgetExceeded(RuntimeError):
    """The exact shared-decay oracle exceeded its budget. Reduce the instance size or select auto or bounds."""



def _validate_oracle_inputs(bases, amps, rates, lengths, kinds, n, checkpoints):
    vectors = [np.asarray(x) for x in (bases, amps, rates, lengths, kinds)]
    if any(x.ndim != 1 for x in vectors) or not vectors[0].size:
        raise ValueError("Per-arm parameters must be nonempty one-dimensional arrays.")
    if any(x.size != vectors[0].size for x in vectors):
        raise ValueError("All per-arm parameter arrays must have the same length.")
    if any(not np.all(np.isfinite(x)) for x in vectors):
        raise ValueError("All per-arm parameters must be finite.")
    if not np.all(np.isin(vectors[4], [0, 1, 2, 3])):
        raise ValueError("Curve codes must be 0 (stationary), 1 (exponential), 2 (power law) or 3 (plateau).")
    if np.any(vectors[3] < 0) or np.any(vectors[3] != np.floor(vectors[3])):
        raise ValueError("Plateau lengths must be nonnegative integers.")
    b, a, p = [np.ascontiguousarray(x, dtype=np.float64) for x in vectors[:3]]
    length, kind = [np.ascontiguousarray(x, dtype=np.int64) for x in vectors[3:]]
    if np.any(a < 0) or np.any(b < 0) or np.any(b > 1):
        raise ValueError("Amplitudes must be nonnegative and limiting mean rewards must lie in [0, 1].")
    active_smooth = ((kind == 1) | (kind == 2)) & (a > 0)
    if np.any(p[active_smooth] <= 0):
        raise ValueError("Exponential rates and power-law exponents must be positive for decaying arms.")
    effective_a = np.where((kind == 0) | ((kind == 3) & (length == 0)), 0.0, a)
    if np.any(b + effective_a > 1 + 1e-12):
        raise ValueError("The Bernoulli mean b+f(1) must not exceed 1.")
    if isinstance(n, (bool, np.bool_)) or not np.isfinite(n) or n < 1 or n != int(n):
        raise ValueError("The number of agents n must be a positive integer.")
    cp = np.asarray(checkpoints)
    if (cp.ndim != 1 or cp.size == 0 or not np.all(np.isfinite(cp))
            or np.any(cp != np.floor(cp)) or cp[0] != 0 or np.any(np.diff(cp) <= 0)):
        raise ValueError("Checkpoints must form a strictly increasing sequence of integers starting at 0.")
    cp = np.ascontiguousarray(cp, dtype=np.int64)
    if cp[-1] > np.iinfo(np.int64).max // int(n):
        raise ValueError("The total pull budget exceeds the int64 range.")
    return b, a, p, length, kind, int(n), cp, effective_a



def _oracle_dp_preflight(n, arm_count, horizon, max_states, max_transitions):
    """All nonnegative count vectors at each layer are reachable, so state and transition counts can be computed exactly in advance."""
    actions = math.comb(n + arm_count - 1, arm_count - 1)
    transitions, previous, peak = 0, 1, 1
    for t in range(1, horizon + 1):
        current = math.comb(n * t + arm_count - 1, arm_count - 1)
        peak = max(peak, previous + current)
        transitions += previous * actions
        if peak > max_states:
            raise OracleBudgetExceeded(
                f"At layer {t}, shared-decay DP needs to store {peak:,} states, exceeding the limit of {max_states:,}")
        if transitions > max_transitions:
            raise OracleBudgetExceeded(
                f"Through layer {t}, shared-decay DP needs {transitions:,} transitions, exceeding the limit of {max_transitions:,}")
        previous = current
    return actions, peak, transitions



def _oracle_allocations(n, arm_count):
    def generate(left, remaining, prefix):
        if remaining == 1:
            yield tuple(prefix + [left])
        else:
            for count in range(left + 1):
                yield from generate(left - count, remaining - 1, prefix + [count])
    return list(generate(n, arm_count, []))



def _public_dp(bases, amps, rates, lengths, kinds, n, checkpoints,
               max_states, max_transitions, max_seconds):
    """Forward Bellman recursion. The maximum at each layer is the optimum for that horizon, computed independently of the terminal optimal path."""
    arm_count, horizon = bases.size, int(checkpoints[-1])
    actions_count, peak_states, expected_transitions = _oracle_dp_preflight(
        n, arm_count, horizon, max_states, max_transitions)
    started = time.perf_counter()
    actions = _oracle_allocations(n, arm_count)
    active_actions = [tuple((k, c) for k, c in enumerate(action) if c)
                      for action in actions]
    states = {(0,) * arm_count: 0.0}
    result, cp, visits = np.zeros(checkpoints.size), 1, 0
    for t in range(1, horizon + 1):
        following = {}
        for state, path_value in states.items():
            means = [curve_mean(kinds[k], bases[k], amps[k], rates[k],
                                lengths[k], state[k] + 1) for k in range(arm_count)]
            for action in active_actions:
                successor = list(state)
                value = path_value
                for k, count in action:
                    successor[k] += count
                    value += count * means[k]
                key = tuple(successor)
                if value > following.get(key, -math.inf):
                    following[key] = value
                visits += 1
                if visits % 1024 == 0 and time.perf_counter() - started > max_seconds:
                    raise OracleBudgetExceeded(f"Shared-decay DP exceeded the time limit of {max_seconds:g} seconds")
        states = following
        if time.perf_counter() - started > max_seconds:
            raise OracleBudgetExceeded(f"Shared-decay DP exceeded the time limit of {max_seconds:g} seconds")
        if cp < checkpoints.size and t == checkpoints[cp]:
            result[cp] = max(states.values())
            cp += 1
    return result, {"dp_actions": actions_count, "dp_peak_states": peak_states,
                    "dp_transitions": visits, "dp_expected_transitions": expected_transitions,
                    "dp_seconds": time.perf_counter() - started}



def compute_oracle(bases, amps, rates, lengths, kinds, n, checkpoints,
                   fatigue, mode="auto", max_states=100000,
                   max_transitions=2000000, max_seconds=20.0):
    """Return lower and upper bounds on team value and JSON-serializable metadata.

    In 'auto' mode, individual decay and convex shared decay curves have exact solutions.
    For other shared curves, try dynamic programming (DP) and return certified bounds if it exceeds the budget.
    In 'exact' mode this raises an error. In 'bounds' mode the general DP is skipped. Budgets apply only to the general DP.

    For convex shared decay curves, the finite-horizon Bellman value is convex in the real-valued counts.
    At a fixed state, the objective is convex in the allocation vector, so some simplex vertex n*e_k is optimal.
    Merge the resulting nonincreasing sequences b_k+f_k(1), b_k+f_k(1+n), ... across arms. This assumes homogeneous
    agents, no collision penalty and rewards based on start-of-round counts. Abrupt plateau drops are excluded.

    For general monotone curves, Vser(n*t) <= V*(t) <= Vser(n*t)+(n-1)*sum f_k(1).
    The feasible greedy policy that assigns all agents to one arm per round can improve the lower bound.
    """
    b, a, p, length, kind, n, cp, effective_a = _validate_oracle_inputs(
        bases, amps, rates, lengths, kinds, n, checkpoints)
    if fatigue in (0, "personal", "private"):
        fatigue = 0
    elif fatigue in (1, "public"):
        fatigue = 1
    else:
        raise ValueError("Supported settings are individual decay (lambda=0) and shared decay (lambda=1).")
    if mode not in ("auto", "exact", "bounds"):
        raise ValueError("Oracle mode must be auto, exact or bounds.")
    if (int(max_states) != max_states or int(max_transitions) != max_transitions
            or max_states < 1 or max_transitions < 1
            or not np.isfinite(max_seconds) or max_seconds <= 0):
        raise ValueError("The state, transition and time limits for shared-decay DP must be positive.")
    info = {"fatigue": int(fatigue), "requested_mode": mode, "exact": True,
            "value_unit": "Cumulative expected team reward", "horizon": int(cp[-1]),
            "agents": n, "arms": int(b.size)}
    if fatigue == 0:
        value = _oracle_greedy_prefix(b, a, p, length, kind, cp, 1, float(n))
        info.update(method="personal_serial_exact", label="Exact serial oracle for individual decay")
        return value, value.copy(), info
    convex = bool(np.all((kind != 3) | (effective_a == 0)))
    if n == 1 or b.size == 1 or convex or cp[-1] <= 1:
        value = _oracle_greedy_prefix(b, a, p, length, kind, cp, n, float(n))
        info.update(method="public_convex_exact" if convex else "public_trivial_exact",
                    label="Exact oracle for convex shared decay curves" if convex else "Exact oracle for a special case of shared decay")
        return value, value.copy(), info
    reason = "Certified bounds were requested in the configuration."
    if mode != "bounds":
        try:
            value, details = _public_dp(b, a, p, length, kind, n, cp,
                                        int(max_states), int(max_transitions), max_seconds)
            info.update(details)
            info.update(method="public_dp_exact", label="Exact dynamic programming oracle for shared decay")
            return value, value.copy(), info
        except OracleBudgetExceeded as exc:
            if mode == "exact":
                raise OracleBudgetExceeded(
                    str(exc) + ". Reduce n, K or T, disable shared decay, or explicitly choose auto or bounds.") from exc
            reason = str(exc)
    serial = _oracle_greedy_prefix(b, a, p, length, kind, cp * n, 1, 1.0)
    feasible = _oracle_greedy_prefix(b, a, p, length, kind, cp, n, float(n))
    lower = np.maximum(serial, feasible)
    initial_max = float(np.max(b + effective_a))
    upper = np.minimum(serial + (n - 1) * float(effective_a.sum()), cp * n * initial_max)
    upper[0] = 0.0
    # Account for roundoff while preserving the theoretical upper bound.
    upper = np.maximum(upper, lower)
    info.update(exact=False, method="public_certified_bounds", label="Certified oracle bounds for shared decay",
                reason=reason, bound_additive=(n - 1) * float(effective_a.sum()),
                max_interval_width=float(np.max(upper - lower)))
    return lower, upper, info



def oracle_self_check():
    """Check convex curves, plateau curves and bounds for general curves against an independent small-scale DP."""
    rng = np.random.default_rng(93271)
    cp = np.arange(5, dtype=np.int64)
    for n in (2, 3):
        for trial in range(6):
            b = rng.uniform(0.1, 0.6, 3)
            a = rng.uniform(0.05, 0.25, 3)
            p = rng.uniform(0.1, 2.0, 3)
            length = np.array([1, 2, 5], dtype=np.int64)
            kinds = np.array([0, 1, 2], dtype=np.int64)
            exact, _, info = compute_oracle(b, a, p, length, kinds, n, cp, 1)
            reference, _ = _public_dp(b, a, p, length, kinds, n, cp,
                                      100000, 2000000, 60.0)
            assert info["exact"] and np.allclose(exact, reference, atol=1e-10)
            kinds[trial % 3] = 3
            exact, _, info = compute_oracle(b, a, p, length, kinds, n, cp, 1, "exact")
            lower, upper, bounds_info = compute_oracle(b, a, p, length, kinds, n, cp, 1, "bounds")
            assert info["exact"] and not bounds_info["exact"]
            assert np.all(lower <= exact + 1e-10) and np.all(exact <= upper + 1e-10)
    b, a = np.array([0.5, 0.25]), np.array([0.0, 0.5])
    p, length, kind = np.ones(2), np.array([0, 4]), np.array([0, 3])
    cp = np.arange(9, dtype=np.int64)
    personal, _, _ = compute_oracle(b, a, p, length, kind, 3, cp, 0)
    assert np.allclose(personal, 3 * (0.5 * cp + 0.25 * np.minimum(cp, 4)))
    fallback, high, info = compute_oracle(b, a, p, length, kind, 3, cp, 1,
                                         max_states=2)
    assert not info["exact"] and np.all(fallback <= high)
    try:
        compute_oracle(b, a, p, length, kind, 3, cp, 1, "exact", max_states=2)
    except OracleBudgetExceeded:
        pass
    else:
        raise AssertionError("Exact mode must raise an error when the oracle budget is exceeded.")
    return True



def eff_fewa_init(n_learners, k, horizon):
    """Return six arrays: counts, current, pending, pending_n, valid, and workspace.

    counts tracks the observations received by the estimator. Adding these counts to the physical pull counts would double-count pulls.
    For centralized FEWA, set n_learners=1 and update the estimator once per batch mean.
    horizon is the maximum number of observations per learner, irrespective of the total number of team pulls.
    An extra unfilled window level provides a stopping condition for arm selection. Memory use is O(n*K*log T).
    """
    if min(n_learners, k, horizon) < 1:
        raise ValueError("FEWA requires positive integers for the number of learners, the number of arms, and the horizon.")
    layers = int(horizon).bit_length() + 1
    shape = (int(n_learners), int(k), layers)
    counts = np.zeros(shape[:2], dtype=np.int64)
    current = np.zeros(shape, dtype=np.float64)
    pending = np.zeros(shape, dtype=np.float64)
    pending_n = np.zeros(shape, dtype=np.int64)
    valid = np.zeros(shape[:2], dtype=np.int64)
    workspace = np.empty(shape[:2], dtype=np.int64)
    return counts, current, pending, pending_n, valid, workspace



@njit(cache=False)
def _fewa_log_confidence(t, k, alpha, delta0, include_k):
    # Work in log space to avoid overflow in t**alpha. Capping delta_t at 1 gives the authors' log+ convention.
    ans = alpha * math.log(max(t, 1)) - math.log(delta0)
    if include_k:
        ans += math.log(k)
    return max(ans, 0.0)



@njit(cache=False)
def eff_fewa_select(agent, t, counts, current, valid, workspace,
                    alpha, delta0, sigma2, include_k):
    """Select an arm, updating only workspace. Break ties by pull count, then arm index."""
    k = counts.shape[1]
    for arm in range(k):
        workspace[agent, arm] = arm
    return _filter_eff_candidates(agent, t, counts, current, valid, workspace, k,
                                  alpha, delta0, sigma2, include_k)


@njit(cache=False)
def _filter_eff_candidates(agent, t, counts, current, valid, workspace, remaining,
                           alpha, delta0, sigma2, include_k):
    """Filter the candidates in workspace. The statistics arrays use global arm indices."""
    k = counts.shape[1]
    logconf = _fewa_log_confidence(t, k, alpha, delta0, include_k)
    layers = current.shape[2]
    for j in range(layers):
        if remaining == 1:
            return workspace[agent, 0]
        # The remaining arms passed all smaller windows. Check whether any lacks statistics at this level.
        # A missing level 0 identifies an unobserved arm. A missing higher level stops the search after the preceding filter.
        chosen = -1
        chosen_n = np.int64(9223372036854775807)
        for pos in range(remaining):
            arm = workspace[agent, pos]
            samples = counts[agent, arm]
            if valid[agent, arm] <= j and (samples < chosen_n or
                                           (samples == chosen_n and arm < chosen)):
                chosen = arm
                chosen_n = samples
        if chosen >= 0:
            return chosen
        best_sum = -math.inf
        for pos in range(remaining):
            arm = workspace[agent, pos]
            best_sum = max(best_sum, current[agent, arm, j])
        window = 1 << j
        threshold = best_sum - math.sqrt(8.0 * sigma2 * window * logconf)
        kept = 0
        for pos in range(remaining):
            arm = workspace[agent, pos]
            if current[agent, arm, j] >= threshold:
                workspace[agent, kept] = arm
                kept += 1
        remaining = kept
    raise RuntimeError("Insufficient capacity for EFF-FEWA statistics. Increase the initial horizon.")



@njit(cache=False)
def eff_raw_ucb_select(agent, current, valid, inv_windows, bonus):
    """EFF-RAW-UCB (m=2): maximize the minimum UCB over the arm's ready windows."""
    chosen = 0
    best_index = -math.inf
    for arm in range(valid.shape[1]):
        ready = valid[agent, arm]
        if ready == 0:
            return arm
        arm_index = math.inf
        for j in range(ready - 1, -1, -1):
            candidate = current[agent, arm, j] * inv_windows[j] + bonus[j]
            arm_index = min(arm_index, candidate)
            # Later arms lose ties. Another window can only decrease this index.
            if arm_index <= best_index:
                break
        if arm_index > best_index:
            chosen, best_index = arm, arm_index
    return chosen


@njit(cache=False)
def eff_fewa_update(agent, arm, reward, counts, current, pending, pending_n, valid):
    """Add one reward or a batch mean for a single arm in O(log T) time. current stores window sums.

    Descending updates use the smaller window's pending sum after adding the new reward and before resetting it.
    This matches the authors' simultaneous copy of adjacent pending sums after accumulation. The window of size 2 inherits the current reward from the window of size 1.
    Each level accumulates its initial prefix and first sets current when it reaches the window size.
    """
    counts[agent, arm] += 1
    for j in range(current.shape[2] - 1, 0, -1):
        pending[agent, arm, j] += reward
        pending_n[agent, arm, j] += 1
        if pending_n[agent, arm, j] == (1 << j):
            current[agent, arm, j] = pending[agent, arm, j]
            if valid[agent, arm] < j + 1:
                valid[agent, arm] = j + 1
            if j == 1:
                pending[agent, arm, j] = reward
                pending_n[agent, arm, j] = 1
            else:
                pending[agent, arm, j] = pending[agent, arm, j - 1] + reward
                pending_n[agent, arm, j] = pending_n[agent, arm, j - 1] + 1
    current[agent, arm, 0] = reward
    pending[agent, arm, 0] = reward
    pending_n[agent, arm, 0] = 1
    if valid[agent, arm] == 0:
        valid[agent, arm] = 1



def exact_fewa_init(n_learners, k, horizon, max_bytes=256 * 1024 * 1024):
    """Initialize the original FEWA with all integer window sizes for small experiments and validation. Check the memory budget.

    Prefix sums allow O(1) window queries. Arm selection takes O(K*T) time in the worst case, and storage is O(n*K*T).
    Exceeding the budget raises an error without truncating the history or switching algorithms.
    """
    if min(n_learners, k, horizon) < 1:
        raise ValueError("FEWA requires positive integers for the number of learners, the number of arms, and the horizon.")
    needed = int(n_learners) * int(k) * (int(horizon) + 1) * 8
    if needed > max_bytes:
        raise MemoryError("FEWA requires %.1f MiB for the prefix-sum array, exceeding the budget. Reduce the problem size or use EFF-FEWA."
                          % (needed / 2**20))
    counts = np.zeros((n_learners, k), dtype=np.int64)
    prefix = np.zeros((n_learners, k, horizon + 1), dtype=np.float64)
    workspace = np.empty((n_learners, k), dtype=np.int64)
    return counts, prefix, workspace



@njit(cache=False)
def exact_fewa_select(agent, t, counts, prefix, workspace,
                      alpha, delta0, sigma2, include_k):
    """Filter at the current window size, then select among survivors with no observations left for a larger window."""
    k = counts.shape[1]
    for arm in range(k):
        workspace[agent, arm] = arm
        if counts[agent, arm] == 0:
            return arm
    remaining = k
    logconf = _fewa_log_confidence(t, k, alpha, delta0, include_k)
    for h in range(1, prefix.shape[2]):
        if remaining == 1:
            return workspace[agent, 0]
        best_sum = -math.inf
        for pos in range(remaining):
            arm = workspace[agent, pos]
            n = counts[agent, arm]
            value = prefix[agent, arm, n] - prefix[agent, arm, n - h]
            best_sum = max(best_sum, value)
        threshold = best_sum - math.sqrt(8.0 * sigma2 * h * logconf)
        kept = 0
        chosen = -1
        for pos in range(remaining):
            arm = workspace[agent, pos]
            n = counts[agent, arm]
            value = prefix[agent, arm, n] - prefix[agent, arm, n - h]
            if value >= threshold:
                workspace[agent, kept] = arm
                kept += 1
                if n == h and chosen < 0:
                    chosen = arm
        if chosen >= 0:
            return chosen
        remaining = kept
    raise RuntimeError("Insufficient capacity for FEWA statistics.")



@njit(cache=False)
def exact_fewa_update(agent, arm, reward, counts, prefix):
    n = counts[agent, arm] + 1
    if n >= prefix.shape[2]:
        raise RuntimeError("Insufficient capacity for FEWA statistics. Increase the horizon.")
    prefix[agent, arm, n] = prefix[agent, arm, n - 1] + reward
    counts[agent, arm] = n



def selfcheck_windows():
    """Check each window sum and arm choice against an independent calculation using the full observation history."""
    rng = np.random.default_rng(130626)
    n, k, horizon = 2, 5, 512
    counts, current, pending, pending_n, valid, workspace = eff_fewa_init(n, k, horizon)
    f_counts, prefix, f_workspace = exact_fewa_init(n, k, horizon)
    history = [[[] for _ in range(k)] for _ in range(n)]
    alpha, delta0, sigma2, include_k = 0.06, 1.0, 0.25, True

    def direct_select(agent, t, efficient):
        candidates = list(range(k))
        h = 1
        logconf = max(alpha * math.log(max(t, 1)) - math.log(delta0) + math.log(k), 0)
        while True:
            if len(candidates) == 1:
                return candidates[0]
            missing = [a for a in candidates if len(history[agent][a]) < h]
            if missing:
                return min(missing, key=lambda a: (len(history[agent][a]), a))
            means = {}
            for a in candidates:
                values = history[agent][a]
                size = len(values)
                if efficient and h > 1:
                    end = size - (size % (h // 2))
                else:
                    end = size
                means[a] = sum(values[end - h:end]) / h
            cutoff = max(means.values()) - math.sqrt(8 * sigma2 * logconf / h)
            candidates = [a for a in candidates if means[a] >= cutoff]
            h = h * 2 if efficient else h + 1

    for t in range(1, horizon + 1):
        for agent in range(n):
            a = eff_fewa_select(agent, t, counts, current, valid, workspace,
                               alpha, delta0, sigma2, include_k)
            assert a == direct_select(agent, t, True), (agent, t, "EFF action")
            b = exact_fewa_select(agent, t, f_counts, prefix, f_workspace,
                                 alpha, delta0, sigma2, include_k)
            assert b == direct_select(agent, t, False), (agent, t, "FEWA action")
            # Give both estimators the same externally generated sequence of arm pulls so adaptive choices cannot confound the check.
            arm = int(rng.integers(k)) if t < horizon // 2 else int((agent + t // 31) % k)
            reward = float(rng.random())
            history[agent][arm].append(reward)
            eff_fewa_update(agent, arm, reward, counts, current, pending, pending_n, valid)
            exact_fewa_update(agent, arm, reward, f_counts, prefix)
            size = len(history[agent][arm])
            for j in range(valid[agent, arm]):
                h = 1 << j
                end = size if h == 1 else size - size % (h // 2)
                expected = sum(history[agent][arm][end - h:end])
                assert np.isclose(current[agent, arm, j], expected, atol=2e-12, rtol=2e-14)
    assert np.array_equal(counts, f_counts)
    assert np.all(counts.sum(axis=1) == horizon)
    # When the first filter can identify a winner, equal minimum sample counts must not stop selection before filtering.
    state = eff_fewa_init(1, 2, 4)
    cc, cur, pp, pn, vv, ws = state
    eff_fewa_update(0, 0, 0.0, cc, cur, pp, pn, vv)
    eff_fewa_update(0, 1, 1.0, cc, cur, pp, pn, vv)
    assert eff_fewa_select(0, 3, cc, cur, vv, ws, 5., 1., 0., True) == 1
    assert eff_fewa_select(0, 3, cc, cur, vv, ws, 5., 1., .25, True) == 0
    total_bytes = sum(arr.nbytes for arr in eff_fewa_init(16, 64, 300_000))
    return {"status": "passed", "observations_checked": n * horizon,
            "large_state_MiB": round(total_bytes / 2**20, 3)}



@njit(cache=False, inline="always")
def uniform01(seed, counter):
    """SplitMix64 counter-based random stream, independent of threading, algorithm order, and the number of communication draws."""
    z = np.uint64(seed) + np.uint64(counter) + np.uint64(0x9E3779B97F4A7C15)
    z = (z ^ (z >> np.uint64(30))) * np.uint64(0xBF58476D1CE4E5B9)
    z = (z ^ (z >> np.uint64(27))) * np.uint64(0x94D049BB133111EB)
    z = z ^ (z >> np.uint64(31))
    return float(z >> np.uint64(11)) * (1.0 / 9007199254740992.0)



@njit(cache=False, nogil=True)
def _ucb_radius_table(T, log_conf):
    radius = np.zeros(T + 1)
    for m in range(1, T + 1):
        radius[m] = math.sqrt(log_conf / (2.0 * m))
    return radius


def prepare_simulation(case, config):
    """Keep read-only quantities shared within a case in memory for this run."""
    n, K, T = case["n"], case["K"], case["T"]
    P = make_network(n, case["network"], config["COMMUNICATION"]["CUSTOM_P"], case["center"])
    cdf = np.cumsum(P, axis=1)
    cdf[:, -1] = 1.0
    H, log_conf, phases = make_schedule(n, K, T, case, config)
    radius = _ucb_radius_table(T, log_conf)
    # Worker threads only read these arrays.
    return dict(cdf=cdf, H=H, log_conf=log_conf, phases=phases, radius=radius)


@njit(cache=False, nogil=True)
def _simulation_kernel(n, T, kinds, bases, amps, rates, lengths, fatigue,
                       mode, cdf, phase_ends, log_conf, reward_seed, comm_seed,
                       times, recent_window, alpha, delta0, sigma2, include_k,
                       wc, current, pending, pending_n, valid, workspace, prefix, radius, wanted):
    K = len(bases)
    track_current = wanted[8] or wanted[17]
    track_history = wanted[9] or wanted[18]
    best_arm = np.argmax(bases)
    gaps = bases[best_arm] - bases
    counts = np.zeros((n, K), np.int64)
    team_counts = np.zeros(K, np.int64)
    cooperative = mode == 0 or mode == 7 or mode == 9
    uses_ucb = mode <= 2 or mode == 9
    sums = np.zeros((n, K)) if uses_ucb else np.zeros((0, 0))
    expected_excess = np.zeros((n, K)) if track_history else np.zeros((0, 0))
    positive = np.zeros(K) if wanted[16] else np.zeros(0)
    phase_counts = np.zeros((n, K), np.int64) if cooperative else np.zeros((0, 0), np.int64)
    indices = np.full((n, K), np.inf) if uses_ucb else np.zeros((0, 0))
    restricted = cooperative or mode == 2
    capacity = min(K, (K + n - 1) // n + 2) if restricted else K
    active = np.full((n, capacity), -1, np.int64)
    sizes = np.zeros(n, np.int64)
    sticky = np.zeros(n, np.int64)
    holding = np.ones(n, np.int64)
    for i in range(n):
        if restricted:
            for k in range(i, K, n):
                active[i, sizes[i]] = k
                sizes[i] += 1
            sticky[i] = sizes[i]
            added = 0
            for k in range(K):
                if k % n != i and added < 2:
                    active[i, sizes[i]] = k
                    sizes[i] += 1
                    added += 1
            holding[i] = 0
            for j in range(sizes[i]):
                if active[i, j] == best_arm:
                    holding[i] = 1
        else:
            sizes[i] = K
            sticky[i] = K
            for k in range(K):
                active[i, k] = k
    held = np.sum(holding)
    first_all = 0 if held == n else -1
    first_90pct = 0 if 10 * held >= 9 * n else -1
    stable_all = first_all
    selected = np.zeros(n, np.int64)
    means = np.zeros(n)
    public_means = np.empty(K)
    for k in range(K):
        public_means[k] = curve_mean(kinds[k], bases[k], amps[k], rates[k], lengths[k], 1)
    changed = np.full(K, -1, np.int64)
    rec = np.zeros(n, np.int64)
    request_counts = np.zeros(n, np.int64)
    reply_counts = np.zeros(n, np.int64)
    phase_correct = np.zeros(len(phase_ends)) if wanted[19] else np.zeros(0)
    phase_bad_holder = np.zeros(len(phase_ends), np.int64) if wanted[20] else np.zeros(0, np.int64)
    pts = len(times)
    # Team value, realized reward, limiting-mean loss, holding fraction, selection fraction, recommendation accuracy, node-rounds missing the best arm,
    # limiting-mean loss while holding the best arm, current bias, historical bias, extra pulls after the plateau, recent best-arm selection fraction, rewards uploaded to the central learner.
    metrics = np.zeros((pts, 13))
    metrics[:, 5] = np.nan
    req_path = np.zeros((pts, n), np.int64) if wanted[13] else np.zeros((0, 0), np.int64)
    rep_path = np.zeros((pts, n), np.int64) if wanted[13] else np.zeros((0, 0), np.int64)
    value_path = np.zeros((pts, n)) if wanted[14] else np.zeros((0, 0))
    public_path = np.zeros((pts, K), np.int64) if wanted[15] else np.zeros((0, 0), np.int64)
    positive_path = np.zeros((pts, K)) if wanted[16] else np.zeros((0, 0))
    bias_path = np.zeros((pts, K)) if wanted[17] else np.zeros((0, 0))
    prefix_bias_path = np.full((pts, K), np.nan) if wanted[18] else np.zeros((0, 0))
    per_value = np.zeros(n) if wanted[14] else np.zeros(0)
    total = 0.0
    realized = 0.0
    bottom = 0.0
    missing = 0
    held_loss = 0.0
    best_pulls = 0
    plateau_excess = 0
    uploads = 0
    accuracy = np.nan
    ring = np.zeros(min(recent_window, T), np.int64) if wanted[11] else np.zeros(0, np.int64)
    recent_sum = 0
    next_cp = 0
    phase = 0
    central = mode == 5 or mode == 6
    raw_layers = current.shape[2] if mode == 8 else 0
    inv_windows = np.empty(raw_layers)
    inv_sqrt_windows = np.empty(raw_layers)
    raw_bonus = np.empty(raw_layers)
    for j in range(raw_layers):
        inv_windows[j] = 1.0 / (1 << j)
        inv_sqrt_windows[j] = math.sqrt(inv_windows[j])
    for step in range(T + 1):
        # Step 0 is the initial state. Later checkpoints include all rounds and scheduled communication through that step.
        if next_cp < pts and step == times[next_cp]:
            cp = next_cp
            metrics[cp, 0] = total
            metrics[cp, 1] = realized
            metrics[cp, 2] = bottom
            metrics[cp, 3] = held / n
            metrics[cp, 4] = best_pulls / (n * max(step, 1))
            metrics[cp, 5] = accuracy
            metrics[cp, 6] = missing
            metrics[cp, 7] = held_loss
            metrics[cp, 10] = plateau_excess
            metrics[cp, 11] = recent_sum / (n * max(1, min(step, recent_window)))
            metrics[cp, 12] = uploads
            if wanted[13]:
                for i in range(n):
                    req_path[cp, i] = request_counts[i]
                    rep_path[cp, i] = reply_counts[i]
            if wanted[14]:
                for i in range(n):
                    value_path[cp, i] = per_value[i]
            if wanted[15]:
                for k in range(K):
                    public_path[cp, k] = team_counts[k]
            if wanted[16]:
                for k in range(K):
                    positive_path[cp, k] = positive[k]
            if track_current or track_history:
                bias_sum = 0.0
                history_sum = 0.0
                seen_pairs = 0
                for k in range(K):
                    arm_current = 0.0
                    arm_history = 0.0
                    arm_seen = 0
                    public_excess = 0.0
                    if track_current and fatigue == 1:
                        public_excess = curve_mean(kinds[k], bases[k], amps[k], rates[k], lengths[k], 1 + team_counts[k]) - bases[k]
                    for i in range(n):
                        if track_current:
                            if fatigue == 0:
                                q = 1 + counts[i, k]
                                arm_current += curve_mean(kinds[k], bases[k], amps[k], rates[k], lengths[k], q) - bases[k]
                            else:
                                # Reuse the shared mean while preserving the original order of summation over agents.
                                arm_current += public_excess
                        if track_history and counts[i, k] > 0:
                            arm_history += expected_excess[i, k] / counts[i, k]
                            arm_seen += 1
                    if wanted[17]:
                        bias_path[cp, k] = arm_current / n
                    bias_sum += arm_current
                    history_sum += arm_history
                    seen_pairs += arm_seen
                    if wanted[18] and arm_seen:
                        prefix_bias_path[cp, k] = arm_history / arm_seen
                metrics[cp, 8] = bias_sum / (n * K)
                metrics[cp, 9] = history_sum / seen_pairs if seen_pairs else np.nan
            next_cp += 1
        if step == T:
            break
        t = step + 1
        if wanted[6]:
            missing += n - held
        if mode == 8:
            logconf = _fewa_log_confidence(t, K, alpha, delta0, include_k)
            scale = math.sqrt(2.0 * sigma2 * logconf)
            for j in range(raw_layers):
                raw_bonus[j] = scale * inv_sqrt_windows[j]
        if central:
            if mode == 5:
                chosen = eff_fewa_select(0, t, wc, current, valid, workspace,
                                         alpha, delta0, sigma2 / n, include_k)
            else:
                chosen = exact_fewa_select(0, t, wc, prefix, workspace,
                                           alpha, delta0, sigma2 / n, include_k)
            for i in range(n):
                selected[i] = chosen
        else:
            for i in range(n):
                if mode == 3:
                    chosen = eff_fewa_select(i, t, wc, current, valid, workspace,
                                             alpha, delta0, sigma2, include_k)
                elif mode == 4:
                    chosen = exact_fewa_select(i, t, wc, prefix, workspace,
                                               alpha, delta0, sigma2, include_k)
                elif mode == 7:
                    for pos in range(sizes[i]):
                        workspace[i, pos] = active[i, pos]
                    chosen = _filter_eff_candidates(i, t, wc, current, valid, workspace, sizes[i],
                                                    alpha, delta0, sigma2, include_k)
                elif mode == 8:
                    chosen = eff_raw_ucb_select(i, current, valid, inv_windows, raw_bonus)
                else:
                    chosen = K
                    max_index = -np.inf
                    for j in range(sizes[i]):
                        k = active[i, j]
                        score = indices[i, k]
                        if score > max_index or (score == max_index and k < chosen):
                            chosen, max_index = k, score
                selected[i] = chosen
        # Compute all means before updating any agent's counts.
        for i in range(n):
            k = selected[i]
            if fatigue == 0:
                means[i] = curve_mean(kinds[k], bases[k], amps[k], rates[k], lengths[k], 1 + counts[i, k])
            else:
                means[i] = public_means[k]
        batch_reward = 0.0
        round_best = 0
        for i in range(n):
            k = selected[i]
            # Under shared decay, the plateau diagnostic uses the means fixed at the start of the round, before any shared counts are updated.
            if wanted[10] and k != best_arm and kinds[k] == 3 and amps[k] > 0 and means[i] == bases[k]:
                plateau_excess += 1
            reward = 1.0 if uniform01(reward_seed, step * n + i) < means[i] else 0.0
            batch_reward += reward
            counts[i, k] += 1
            team_counts[k] += 1
            if cooperative:
                phase_counts[i, k] += 1
            if uses_ucb:
                sums[i, k] += reward
            if track_history or wanted[16]:
                excess = means[i] - bases[k]
                if track_history:
                    expected_excess[i, k] += excess
                if wanted[16] and k != best_arm:
                    positive[k] += max(0.0, excess - gaps[k] / 2.0)
            if uses_ucb:
                m = counts[i, k]
                indices[i, k] = sums[i, k] / m + radius[m]
            elif mode == 3 or mode == 7 or mode == 8:
                eff_fewa_update(i, k, reward, wc, current, pending, pending_n, valid)
            elif mode == 4:
                exact_fewa_update(i, k, reward, wc, prefix)
            if wanted[14]:
                per_value[i] += means[i]
            if wanted[0]:
                total += means[i]
            if wanted[1]:
                realized += reward
            if wanted[2]:
                bottom += gaps[k]
            if wanted[7] and holding[i]:
                held_loss += gaps[k]
            if (wanted[4] or wanted[11]) and k == best_arm:
                best_pulls += 1
                round_best += 1
        if central:
            if mode == 5:
                eff_fewa_update(0, selected[0], batch_reward / n, wc, current, pending, pending_n, valid)
            else:
                exact_fewa_update(0, selected[0], batch_reward / n, wc, prefix)
            if wanted[12]:
                uploads += n
        if fatigue == 1:
            for i in range(n):
                k = selected[i]
                if changed[k] != step:
                    public_means[k] = curve_mean(kinds[k], bases[k], amps[k], rates[k], lengths[k], 1 + team_counts[k])
                    changed[k] = step
        if wanted[11]:
            ring_pos = step % len(ring)
            recent_sum += round_best - ring[ring_pos]
            ring[ring_pos] = round_best
        if cooperative and n > 1 and phase < len(phase_ends) and t == phase_ends[phase]:
            correct = 0
            bad_holder = 0
            # Cache every agent's recommendation before processing any incoming message.
            for i in range(n):
                if mode == 9:
                    # Disjoint counter range keeps the contact stream paired across policies.
                    rec_counter = np.uint64(phase * n + i) | np.uint64(0x8000000000000000)
                    slot = int(uniform01(comm_seed, rec_counter) * sizes[i])
                    chosen = active[i, slot]
                else:
                    chosen = K
                    best_count = -1
                    for j in range(sizes[i]):
                        k = active[i, j]
                        c = phase_counts[i, k]
                        if c > best_count or (c == best_count and k < chosen):
                            chosen, best_count = k, c
                rec[i] = chosen
                if chosen == best_arm:
                    correct += 1
                elif holding[i]:
                    bad_holder = 1
            accuracy = correct / n
            if wanted[19]:
                phase_correct[phase] = accuracy
            if wanted[20]:
                phase_bad_holder[phase] = bad_holder
            for i in range(n):
                u = uniform01(comm_seed, phase * n + i)
                contact = n - 1
                for j in range(n):
                    if u < cdf[i, j]:
                        contact = j
                        break
                if wanted[13]:
                    request_counts[i] += 1
                    reply_counts[contact] += 1
                incoming = rec[contact]
                present = False
                for j in range(sizes[i]):
                    if active[i, j] == incoming:
                        present = True
                        break
                if not present:
                    if sizes[i] == sticky[i]:
                        active[i, sticky[i]] = incoming
                        sizes[i] = sticky[i] + 1
                    else:
                        kept = K
                        best_count = -1
                        for j in range(sticky[i], sizes[i]):
                            k = active[i, j]
                            c = phase_counts[i, k]
                            if c > best_count or (c == best_count and k < kept):
                                kept, best_count = k, c
                        active[i, sticky[i]] = kept
                        active[i, sticky[i] + 1] = incoming
                        sizes[i] = sticky[i] + 2
                holding[i] = 0
                for j in range(sizes[i]):
                    if active[i, j] == best_arm:
                        holding[i] = 1
            was_all = held == n
            held = np.sum(holding)
            if first_90pct < 0 and 10 * held >= 9 * n:
                first_90pct = t
            if held == n:
                if first_all < 0:
                    first_all = t
                if not was_all:
                    stable_all = t
            else:
                stable_all = -1
            phase_counts.fill(0)
            phase += 1
    return (metrics, counts, req_path, rep_path, value_path, public_path,
            positive_path, bias_path, prefix_bias_path, phase_correct[:phase],
            phase_bad_holder[:phase], first_all, stable_all, first_90pct)

def _window_parameters(config, algorithm):
    """Merge shared window parameters with optional overrides and validate the four effective values."""
    base = config["WINDOW"]
    unified = config.get("UNIFY_WINDOW_PARAMS", False)
    if not isinstance(unified, (bool, np.bool_)):
        raise ValueError("UNIFY_WINDOW_PARAMS must be True or False.")
    overrides = {}
    prefix = ""
    if not unified:
        if algorithm == "central_fewa":
            overrides, prefix = base, "CENTRAL_"
        elif algorithm == "eff_raw_ucb":
            overrides = config.get("RAW_UCB", {})
    values = {}
    for key in ("ALPHA", "DELTA0", "SIGMA2", "INCLUDE_K"):
        override = overrides.get(prefix + key)
        values[key] = base[key] if override is None else override
    for key in ("ALPHA", "DELTA0", "SIGMA2"):
        value = values[key]
        if (not isinstance(value, (int, float, np.integer, np.floating))
                or isinstance(value, (bool, np.bool_)) or not np.isfinite(value)):
            raise ValueError(f"Window parameter {key} for {algorithm} must be a finite number.")
    if values["ALPHA"] <= 0 or not 0 < values["DELTA0"] <= 1 or values["SIGMA2"] < 0.25:
        raise ValueError(f"Window parameters for {algorithm} must satisfy ALPHA > 0, 0 < DELTA0 <= 1, and SIGMA2 >= 0.25.")
    if not isinstance(values["INCLUDE_K"], (bool, np.bool_)):
        raise ValueError(f"Window parameter INCLUDE_K for {algorithm} must be True or False.")
    return values


def simulate_algorithm(algorithm, case, instance, fatigue, times, reward_seed, comm_seed, config,
                       required_metrics=None, prepared=None):
    """Record only the requested metrics while preserving the learning trajectory obtained with full recording."""
    n, K, T = case["n"], case["K"], case["T"]
    mode = ALGORITHM_IDS[algorithm]
    win = config["WINDOW"]
    if algorithm == "central_fewa":
        if fatigue != 1:
            raise ValueError("The centralized same-arm window baseline requires shared decay.")
        mode = 5 if win["CENTRAL_ENGINE"] == "eff_fewa" else 6
    options = _window_parameters(config, algorithm)
    alpha, delta0, sigma2, include_k = (
        options[key] for key in ("ALPHA", "DELTA0", "SIGMA2", "INCLUDE_K"))
    learners = 1 if mode in (5, 6) else n
    wc = np.zeros((1, 1), np.int64)
    current = np.zeros((1, 1, 1))
    pending = np.zeros((1, 1, 1))
    pending_n = np.zeros((1, 1, 1), np.int64)
    valid = np.zeros((1, 1), np.int64)
    workspace = np.zeros((1, 1), np.int64)
    prefix = np.zeros((1, 1, 1))
    if mode in (3, 5, 7, 8):
        wc, current, pending, pending_n, valid, workspace = eff_fewa_init(learners, K, T)
    elif mode in (4, 6):
        if T > win["EXACT_FEWA_MAX_T"]:
            raise ValueError("The horizon exceeds EXACT_FEWA_MAX_T for FEWA. Reduce T or select EFF-FEWA explicitly.")
        wc, prefix, workspace = exact_fewa_init(learners, K, T,
            int(win["MAX_MEMORY_MB_PER_RUN"] * 2**20))
    window_bytes = sum(x.nbytes for x in (wc,current,pending,pending_n,valid,workspace,prefix))
    if window_bytes > win["MAX_MEMORY_MB_PER_RUN"] * 2**20:
        raise MemoryError("Window statistics exceed the per-run memory budget. Reduce the problem size or adjust the WINDOW budget.")
    if prepared is None:
        prepared = prepare_simulation(case, config)
    cdf, H, log_conf, phases, radius = (prepared[key] for key in ("cdf", "H", "log_conf", "phases", "radius"))
    keys = ["team_value","realized_team","bottom_loss","holding_fraction",
            "selection_fraction","recommendation_accuracy","missing_node_rounds",
            "holding_bottom_loss","current_bias","history_bias","plateau_extra_pulls",
            "recent_selection_fraction","reward_uploads"]
    path_groups = [
        {"requests", "replies", "transmissions", "payload_bits", "total_messages"},
        {"individual_value"}, {"public_counts"}, {"positive_excess"},
        {"current_bias_by_arm"}, {"history_bias_by_arm"},
        {"recommendation_times", "phase_correct_fraction"}, {"phase_bad_holder"}]
    selected_keys = None if required_metrics is None else set(required_metrics)
    if selected_keys is not None:
        known = set(keys).union(*path_groups, {"first_all_time", "stable_through_T_time",
                                                "first_90pct_hold_time", "times", "final_counts", "n", "H"})
        unknown = selected_keys - known
        if unknown:
            raise ValueError("Unknown plot metrics: " + ", ".join(sorted(unknown)))
    wanted = np.ones(21, dtype=np.bool_) if selected_keys is None else np.array(
        [key in selected_keys for key in keys] + [bool(group & selected_keys) for group in path_groups], dtype=np.bool_)
    out = _simulation_kernel(n,T,instance["kinds"],instance["bases"],instance["amps"],
        instance["rates"],instance["lengths"],fatigue,mode,cdf,phases,log_conf,
        np.uint64(reward_seed),np.uint64(comm_seed),times,
        max(1,min(T,int(config["EXECUTION"]["RECENT_WINDOW"]))),
        alpha,delta0,sigma2,include_k,
        wc,current,pending,pending_n,valid,workspace,prefix,radius,wanted)
    result = {key: out[0][:, j].copy() for j, key in enumerate(keys) if wanted[j]}
    result.update(times=times.copy(), final_counts=out[1], n=np.int64(n), H=np.int64(H))
    def need(key):
        return selected_keys is None or key in selected_keys
    for key, value in (("requests", out[2]), ("replies", out[3]),
                       ("individual_value", out[4]), ("public_counts", out[5]),
                       ("positive_excess", out[6]), ("current_bias_by_arm", out[7]),
                       ("history_bias_by_arm", out[8]), ("phase_correct_fraction", out[9]),
                       ("phase_bad_holder", out[10])):
        if need(key):
            result[key] = value
    if need("transmissions"):
        result["transmissions"] = out[3].copy()
    if need("payload_bits"):
        result["payload_bits"] = out[3] * int(math.ceil(math.log2(K))) if K > 1 else out[3] * 0
    if need("total_messages"):
        result["total_messages"] = out[2] + out[3]
    if need("recommendation_times"):
        result["recommendation_times"] = phases[:len(out[9])]
    if need("first_all_time"):
        result["first_all_time"] = np.int64(out[11])
    if need("stable_through_T_time"):
        result["stable_through_T_time"] = np.int64(out[12])
    if need("first_90pct_hold_time"):
        result["first_90pct_hold_time"] = np.int64(out[13])
    if int(out[1].sum()) != n*T or not np.all(out[1].sum(axis=1) == T):
        raise AssertionError("The total number of physical arm pulls must equal n*T.")
    return result


@njit(cache=False, nogil=True)
def _communication_paths(n, times, phases, cdf, comm_seed):
    """Replay only the contact stream. As in the full simulation, communication takes effect before the round is recorded."""
    requests = np.zeros((len(times), n), np.int64)
    replies = np.zeros((len(times), n), np.int64)
    received = np.zeros(n, np.int64)
    phase = 0
    for cp in range(len(times)):
        if n > 1:
            while phase < len(phases) and phases[phase] <= times[cp]:
                for i in range(n):
                    u = uniform01(comm_seed, phase * n + i)
                    contact = n - 1
                    for j in range(n):
                        if u < cdf[i, j]:
                            contact = j
                            break
                    received[contact] += 1
                phase += 1
        for i in range(n):
            requests[cp, i] = phase
            replies[cp, i] = received[i]
    return requests, replies


def simulate_communication(algorithm, case, times, comm_seed, config, prepared=None):
    """Count messages independently of rewards and arm choices, using the original schedule, seed, and sequence of sampled contacts."""
    if algorithm not in ALGORITHM_IDS:
        raise ValueError("Communication statistics are unavailable for this algorithm: " + str(algorithm))
    n, K, T = case["n"], case["K"], case["T"]
    if prepared is None:
        H, _, phases = make_schedule(n, K, T, case, config)
        cdf = np.cumsum(make_network(n, case["network"],
            config["COMMUNICATION"]["CUSTOM_P"], case["center"]), axis=1)
        cdf[:, -1] = 1.0
    else:
        H, phases, cdf = prepared["H"], prepared["phases"], prepared["cdf"]
    if algorithm in RECOMMENDING_ALGORITHMS:
        requests, replies = _communication_paths(n, times, phases, cdf, np.uint64(comm_seed))
    else:
        requests = np.zeros((len(times), n), np.int64)
        replies = np.zeros_like(requests)
    return dict(times=times.copy(), requests=requests, replies=replies,
        transmissions=replies.copy(),
        payload_bits=replies * int(math.ceil(math.log2(K))) if K > 1 else replies * 0,
        total_messages=requests + replies,
        reward_uploads=(n * times).astype(np.float64) if algorithm == "central_fewa"
                       else np.zeros(len(times)),
        n=np.int64(n), H=np.int64(H))


def selfcheck_communication(config):
    """Check communication counts against a small full simulation, entry by entry, without writing files."""
    c = copy.deepcopy(config)
    c.update(N_AGENTS=3, N_ARMS=5, HORIZON=41, QUICK_CHECK=False)
    c["GROUPS"] = {name: name == "basic" for name in c["GROUPS"]}
    c["INSTANCE"]["BEST_ARM"] = None
    c["INSTANCE"]["MANUAL"] = {name: None for name in c["INSTANCE"]["MANUAL"]}
    c["COMMUNICATION"].update(NETWORK="complete", STAR_CENTER=0,
                              H=1, SCHEDULE="fixed", FIXED_H=3)
    c["WINDOW"]["EXACT_FEWA_MAX_T"] = max(41, c["WINDOW"]["EXACT_FEWA_MAX_T"])
    case = build_cases(c)[0]
    instance = make_instance(case, c)
    times = np.array([0, 1, 2, 3, 4, 11, 12, 13, 27, 40, 41], dtype=np.int64)
    keys = ("requests", "replies", "transmissions", "payload_bits",
            "total_messages", "reward_uploads")
    for network in ("complete", "ring", "star"):
        own_case = dict(case, network=network, center=1)
        for fatigue in (0, 1):
            for name in ("bgosine", "full_ucb", "eff_fewa", "no_comm", "central_fewa",
                         "coop_eff_fewa", "eff_raw_ucb", "random_rec"):
                if name == "central_fewa" and fatigue == 0:
                    continue
                full = simulate_algorithm(name, own_case, instance, fatigue, times,
                                          np.uint64(123), np.uint64(456), c)
                direct = simulate_communication(name, own_case, times, np.uint64(456), c)
                for key in keys:
                    if not np.array_equal(full[key], direct[key]):
                        raise AssertionError("Communication counts differ from the full simulation: " + network + "/" + name + "/" + key)
    return "Communication self-check passed. Message counts match at every checkpoint with the original schedule and random stream."


def _jsonable(value):
    if isinstance(value, dict):
        return {str(k): _jsonable(v) for k,v in value.items()}
    if isinstance(value, (tuple,list)):
        return [_jsonable(v) for v in value]
    if isinstance(value, np.ndarray):
        return value.tolist()
    if isinstance(value, np.generic):
        return value.item()
    if isinstance(value, Path):
        return str(value)
    return value



def _digest(value, size=12):
    raw = json.dumps(_jsonable(value), ensure_ascii=False, sort_keys=True,
                     separators=(",", ":"), allow_nan=False).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()[:size]



def _positive_integer(value, name, minimum=1):
    if isinstance(value, (bool,np.bool_)) or not isinstance(value, (int,np.integer)) or value < minimum:
        raise ValueError(f"{name} must be an integer greater than or equal to {minimum}.")



def validate_config(c):
    for key in ("N_AGENTS","N_ARMS","HORIZON"):
        _positive_integer(c[key],key)
    _positive_integer(c["SEED"],"SEED",0)
    for key,value in c["REPEATS"].items():
        _positive_integer(value,"REPEATS."+key)
    if c["EXECUTION"]["WORKERS"] != "auto":
        _positive_integer(c["EXECUTION"]["WORKERS"], "EXECUTION.WORKERS")
    for key in ("CHECKPOINTS","RECENT_WINDOW","PROGRESS_EVERY"):
        _positive_integer(c["EXECUTION"][key],"EXECUTION."+key)
    _positive_integer(c["EXECUTION"]["LOG_CHECKPOINTS"],"LOG_CHECKPOINTS",0)
    hours = c["EXECUTION"]["MAX_HOURS"]
    if hours is not None and (not np.isfinite(hours) or hours <= 0):
        raise ValueError("MAX_HOURS must be positive or None.")
    if not (c["RUN_LAMBDA_0"] or c["RUN_LAMBDA_1"]):
        raise ValueError("Enable at least one decay setting.")
    known = set(ALGORITHM_IDS)
    if set(c["ALGORITHMS"]) - known:
        raise ValueError("ALGORITHMS contains an unknown algorithm.")
    if not any(c["ALGORITHMS"].values()):
        raise ValueError("Enable at least one algorithm.")
    for section in ("GROUPS","ALGORITHMS"):
        if any(not isinstance(v,(bool,np.bool_)) for v in c[section].values()):
            raise ValueError(section+" switches must be True or False.")
    only_bgosine = c["OUTPUT"].get("ONLY_BGOSINE_PLOTS", False)
    if not isinstance(only_bgosine, (bool, np.bool_)):
        raise ValueError("OUTPUT.ONLY_BGOSINE_PLOTS must be True or False.")
    if only_bgosine and not c["ALGORITHMS"].get("bgosine", False):
        raise ValueError("Enable ALGORITHMS.bgosine to output only plots that include B-GosInE.")
    extra_plots = c["OUTPUT"].get("EXTRA_BASIC_PLOTS", [])
    allowed_extra = {"03_team_cumulative_pseudo_regret", "05_limiting_mean_loss", "07_recommendation_accuracy",
                     "10_cumulative_expected_reward", "12_selection_loss_when_optimal_arm_available", "14_message_count_and_payload_bits"}
    if not isinstance(extra_plots, (list, tuple)) or any(
            not isinstance(stem, str) or _LEGACY_PLOT_STEMS.get(stem, stem) not in allowed_extra for stem in extra_plots):
        raise ValueError("OUTPUT.EXTRA_BASIC_PLOTS must list names from the six supported supplementary plots.")
    if not (c["OUTPUT"]["SAVE_PLOTS"] or c["OUTPUT"]["SHOW_PLOTS"]):
        raise ValueError("Enable SAVE_PLOTS, SHOW_PLOTS, or both.")
    _positive_integer(c["OUTPUT"]["DPI"], "OUTPUT.DPI")
    com = c["COMMUNICATION"]
    if com["NETWORK"] not in ("complete","ring","star","custom"):
        raise ValueError("Unknown network topology.")
    if com["SCHEDULE"] not in ("scaled","fixed"):
        raise ValueError("SCHEDULE must be 'scaled' or 'fixed'.")
    _positive_integer(com["H"],"communication interval h")
    _positive_integer(com["FIXED_H"],"fixed H")
    if not np.isfinite(com["XI"]) or com["XI"] <= 0 or not np.isfinite(com["BETA"]) or com["BETA"] <= 1:
        raise ValueError("XI must be positive and BETA must exceed 1.")
    if com["DELTA"] is not None and not 0 < com["DELTA"] < 1:
        raise ValueError("DELTA must lie in (0, 1) or be None.")
    if c["ORACLE"]["PUBLIC_MODE"] not in ("auto","exact","bounds"):
        raise ValueError("PUBLIC_MODE must be 'auto', 'exact', or 'bounds'.")
    w = c["WINDOW"]
    for algorithm in ("eff_fewa", "eff_raw_ucb", "central_fewa"):
        _window_parameters(c, algorithm)
    if w["CENTRAL_ENGINE"] not in ("eff_fewa","fewa"):
        raise ValueError("CENTRAL_ENGINE must be 'eff_fewa' or 'fewa'.")
    ins = c["INSTANCE"]
    if ins["FAMILY"] not in FAMILY_IDS or not ins["MIXED_FAMILIES"] or any(f not in FAMILY_IDS for f in ins["MIXED_FAMILIES"]):
        raise ValueError("INSTANCE contains an unknown curve family.")
    if not 0 < ins["BASE_BEST"] <= 1 or not 0 < ins["GAP"] < ins["BASE_BEST"]:
        raise ValueError("The parameters must satisfy 0 < GAP < BASE_BEST <= 1.")
    if not 0 < ins["CONFLICT_FRACTION"] <= 1 or ins["INITIAL_ADVANTAGE"] <= 0:
        raise ValueError("CONFLICT_FRACTION must lie in (0, 1] and INITIAL_ADVANTAGE must be positive.")
    for key in ("RATE_MULTIPLIER_RANGE","RANDOM_GAP_RANGE"):
        values=ins[key]
        if len(values)!=2 or not 0 < values[0] <= values[1]:
            raise ValueError(key+" must give positive lower and upper endpoints in nondecreasing order.")
    if ins["RANDOM_GAP_RANGE"][1] >= ins["BASE_BEST"]:
        raise ValueError("The upper endpoint of RANDOM_GAP_RANGE must be below the optimal limiting mean.")
    for key in ("EXP_RATE","POWER_EXPONENT"):
        if not np.isfinite(ins[key]) or ins[key]<=0:
            raise ValueError(key+" must be finite and positive.")
    _positive_integer(ins["PLATEAU_LENGTH"],"PLATEAU_LENGTH")
    for key in ("AMPLITUDE","BEST_AMPLITUDE"):
        if not np.isfinite(ins[key]) or ins[key]<0:
            raise ValueError(key+" must be finite and nonnegative.")
    for key in ("MAX_STATES","MAX_TRANSITIONS"):
        _positive_integer(c["ORACLE"][key],"ORACLE."+key)
    for key in ("MAX_SECONDS",):
        if not np.isfinite(c["ORACLE"][key]) or c["ORACLE"][key]<=0:
            raise ValueError("ORACLE."+key+" must be finite and positive.")
    for key in ("EXACT_FEWA_MAX_T",):
        _positive_integer(w[key],"WINDOW."+key)
    if not np.isfinite(w["MAX_MEMORY_MB_PER_RUN"]) or w["MAX_MEMORY_MB_PER_RUN"]<=0:
        raise ValueError("WINDOW.MAX_MEMORY_MB_PER_RUN must be finite and positive.")
    if not any(c["GROUPS"].values()):
        raise ValueError("Enable at least one experiment group.")



def make_network(n, kind, custom=None, center=0):
    if n == 1:
        return np.ones((1,1))
    if not 0 <= center < n:
        raise ValueError("STAR_CENTER is outside the node index range.")
    if kind == "complete":
        P = (np.ones((n,n))-np.eye(n))/(n-1)
    elif kind == "ring":
        P = np.zeros((n,n))
        for i in range(n):
            P[i,(i-1)%n] += .5
            P[i,(i+1)%n] += .5
    elif kind == "star":
        P = np.zeros((n,n))
        for i in range(n):
            if i != center:
                P[i,center] = 1.0
                P[center,i] = 1.0/(n-1)
    elif kind == "custom":
        P = np.asarray(custom,dtype=float)
    else:
        raise ValueError("Unknown communication network: "+str(kind))
    if P.shape != (n,n) or not np.all(np.isfinite(P)) or np.any(P < 0) or not np.allclose(P.sum(axis=1),1.0,rtol=0,atol=1e-12):
        raise ValueError("The communication matrix must be a finite, nonnegative n-by-n row-stochastic matrix. Supply custom P at the required size.")
    # Test irreducibility: node 0 must reach every node in both the graph and its transpose.
    for graph in (P>0,P.T>0):
        reached={0}
        pending_nodes=[0]
        while pending_nodes:
            node=pending_nodes.pop()
            for other in np.flatnonzero(graph[node]):
                if int(other) not in reached:
                    reached.add(int(other)); pending_nodes.append(int(other))
        if len(reached)!=n:
            raise ValueError("The communication matrix must be irreducible to satisfy the propagation assumption in the paper.")
    return np.ascontiguousarray(P)



def make_schedule(n,K,T,case,c):
    delta = c["COMMUNICATION"]["DELTA"]
    delta = (T+1.0)**-2 if delta is None else delta
    log_conf = math.log(2.0*n*K*T/delta)
    h=case["h"]
    if case["schedule"]=="scaled":
        H=h*max(1,math.ceil(case["xi"]*log_conf/h))
    else:
        H=case["fixed_H"]
        if H % h:
            raise ValueError(f"Fixed H={H} must be an integer multiple of the communication interval h={h}.")
    boundaries=[]
    ell=1
    while True:
        end=H*math.ceil(ell**case["beta"])
        if end>=T:
            break
        boundaries.append(end)
        ell+=1
    return H,log_conf,np.asarray(boundaries,dtype=np.int64)



def make_checkpoints(T,c):
    linear=np.linspace(0,T,min(T+1,c["EXECUTION"]["CHECKPOINTS"]),dtype=np.int64)
    logs=c["EXECUTION"]["LOG_CHECKPOINTS"]
    geometric=np.geomspace(1,T,min(T,logs)).astype(np.int64) if logs else np.empty(0,np.int64)
    return np.unique(np.r_[0,linear,geometric,T]).astype(np.int64)



# The original experiment included display labels in case IDs and random seeds.
# Recover their historical hash input without exposing it in figures or reports.
# Longer phrases precede shorter phrases that can occur within them.
_CASE_HASH_LABELS = (
    ("Increasing horizon at fixed plateau length", "\u56fa\u5b9a\u5e73\u53f0\u5ef6\u957f\u65f6\u57df"),
    ("Fixed number of sticky arms per agent, n=", "\u6bcf\u4eba\u6c38\u4e45\u81c2\u6570\u56fa\u5b9a\uff0cn="),
    ("Varying the number of agents at fixed K/n", "\u56fa\u5b9aK/n\u6539\u53d8\u4eba\u6570"),
    ("Varying the number of agents at fixed K", "\u56fa\u5b9a\u81c2\u6570\u6539\u53d8\u4eba\u6570"),
    ("Horizon proportional to plateau length", "\u5e73\u53f0\u957f\u5ea6\u968f\u65f6\u57df\u53d8\u5316"),
    ("Varying the number of arms at fixed n", "\u56fa\u5b9a\u4eba\u6570\u6539\u53d8\u81c2\u6570"),
    ("Communication opportunity interval", "\u73af\u5883\u901a\u4fe1\u95f4\u9694"),
    (", optimal arm initially at the hub", "\uff0c\u6700\u4f18\u81c2\u6301\u6709\u4eba\u5728\u4e2d\u5fc3"),
    (", optimal arm initially at a leaf", "\uff0c\u6700\u4f18\u81c2\u6301\u6709\u4eba\u5728\u53f6\u8282\u70b9"),
    ("Stationary arms with small gaps", "\u5e73\u7a33\u5c0f\u95f4\u9699"),
    ("Shared decay (exponential), n=", "\u516c\u5171\u4f7f\u7528\u673a\u5236 exp\uff0cn="),
    ("Shared decay (power-law), n=", "\u516c\u5171\u4f7f\u7528\u673a\u5236 power\uff0cn="),
    ("Topology and starting node", "\u7f51\u7edc\u4e0e\u8d77\u70b9"),
    ("Fixed number of agents, K=", "\u56fa\u5b9a\u4eba\u6570\uff0cK="),
    (" / communication interval", "\u901a\u4fe1\u95f4\u9694"),
    ("Shared decay: exponential", "\u516c\u5171\u4f7f\u7528\u673a\u5236exp"),
    ("Fixed number of arms, n=", "\u56fa\u5b9a\u81c2\u6570\uff0cn="),
    ("Fixed plateau length L=", "\u56fa\u5b9a\u5e73\u53f0 L="),
    ("Shared decay: power-law", "\u516c\u5171\u4f7f\u7528\u673a\u5236power"),
    (" / schedule multiplier", "\u65e5\u7a0b\u7cfb\u6570"),
    ("Plateau instances, L=", "\u5e73\u53f0\u65cf L="),
    ("Baseline performance", "\u57fa\u7840\u6027\u80fd"),
    ("Schedule multiplier", "\u65e5\u7a0b\u7cfb\u6570"),
    ("Power-law exponent", "\u5e42\u5f8b\u6307\u6570"),
    ("Limiting-mean gap", "\u5e95\u503c\u95f4\u9699"),
    ("Exponential decay", "\u6307\u6570\u8870\u51cf"),
    ("Network topology", "\u7f51\u7edc\u7ed3\u6784"),
    ("Number of agents", "\u4eba\u6570"),
    ("Random instance ", "\u968f\u673a\u5b9e\u4f8b"),
    ("Power-law decay", "\u5e42\u5f8b\u8870\u51cf"),
    ("Plateau length", "\u5e73\u53f0\u957f\u5ea6"),
    ("Complete graph", "\u5b8c\u5168\u56fe"),
    ("Baseline decay", "\u57fa\u7840\u8870\u51cf"),
    ("Stationary, Δ=", "\u5e73\u7a33\u0394="),
    ("Number of arms", "\u81c2\u6570"),
    ("Time horizon", "\u7ec8\u7aef\u65f6\u57df"),
    ("Decay rate", "\u8870\u51cf\u901f\u7387"),
    ("Ring graph", "\u73af\u5f62"),
    ("Star graph", "\u661f\u5f62"),
    (", H=h", "\uff0cH=h"),
    (", T=", "\uff0cT="),
    (", ξ=", "\uff0c\u03be="),
    (", h=", "\uff0ch="),
    (", K=", ",K="),
)


def _legacy_hash_fields(fields):
    """Recover the original text inputs to the case hash used for paired runs."""
    result = dict(fields)
    for key in ("label", "title", "sweep_group", "sweep_label", "sweep_x"):
        value = result.get(key)
        if isinstance(value, str):
            for label, original in _CASE_HASH_LABELS:
                value = value.replace(label, original)
            result[key] = value
    return result


def build_cases(c):
    com,ins,scan=c["COMMUNICATION"],c["INSTANCE"],c["SCANS"]
    base={"n":c["N_AGENTS"],"K":c["N_ARMS"],"T":c["HORIZON"],
          "family":ins["FAMILY"],"gap":ins["GAP"],"exp_rate":ins["EXP_RATE"],
          "power":ins["POWER_EXPONENT"],"plateau_L":ins["PLATEAU_LENGTH"],
          "network":com["NETWORK"],"center":com["STAR_CENTER"],"h":com["H"],
          "schedule":com["SCHEDULE"],"xi":com["XI"],"fixed_H":com["FIXED_H"],
          "beta":com["BETA"],"instance_index":0,"instance_kind":"fixed",
          "repeat_count":c["REPEATS"]["MAIN"],"star_start":None,
          "force_pure":False,"platform_special":False}
    cases=[]
    def add(group,label,**changes):
        case=dict(base,group=group,label=label)
        case.update(changes)
        if c["QUICK_CHECK"]:
            case.update(n=min(case["n"],4),K=min(case["K"],8),T=min(case["T"],300),repeat_count=3)
            case["center"]=min(case["center"],case["n"]-1)
            if case["platform_special"]:
                case["plateau_L"]=min(case["plateau_L"],100)
        case["case_id"]=group+"_"+_digest(_legacy_hash_fields({k:v for k,v in case.items() if k!="repeat_count"}),10)
        case["title"]=label
        cases.append(case)
    enabled=c["GROUPS"]
    if enabled["basic"]:
        add("basic","Baseline performance")
    if enabled["small_gap"]:
        for gap in scan["GAPS"]:
            add("small_gap",f"Stationary arms with small gaps Δ={gap:g}",family="stationary",gap=gap,
                force_pure=True,repeat_count=c["REPEATS"]["SMALL_GAP"],
                sweep_group="Stationary arms with small gaps",sweep_x=gap,sweep_label="Limiting-mean gap")
    if enabled["plateau"]:
        for L in scan["PLATEAU_LENGTHS"]:
            add("plateau",f"Plateau instances, L={L}",n=2,K=2,T=int(scan["PLATEAU_T_RATIO"]*L),
                family="plateau",plateau_L=L,force_pure=True,platform_special=True,
                network="complete",center=0,repeat_count=c["REPEATS"]["PLATEAU"],
                sweep_group="Horizon proportional to plateau length",sweep_x=L,sweep_label="Plateau length")
        for T in scan["PLATEAU_HORIZONS"]:
            add("plateau",f"Fixed plateau length L={scan['FIXED_PLATEAU_L']}, T={T}",n=2,K=2,T=T,
                family="plateau",plateau_L=scan["FIXED_PLATEAU_L"],force_pure=True,
                platform_special=True,network="complete",center=0,repeat_count=c["REPEATS"]["PLATEAU"],
                sweep_group="Increasing horizon at fixed plateau length",sweep_x=T,sweep_label="Time horizon")
    if enabled["decay"]:
        for rate in scan["EXP_RATES"]:
            add("decay",f"Exponential decay η={rate:g}",family="exp",exp_rate=rate,force_pure=True,
                sweep_group="Exponential decay",sweep_x=rate,sweep_label="Decay rate")
        for p in scan["POWER_EXPONENTS"]:
            add("decay",f"Power-law decay α={p:g}",family="power",power=p,force_pure=True,
                sweep_group="Power-law decay",sweep_x=p,sweep_label="Power-law exponent")
    if enabled["network"]:
        for network in scan["NETWORKS"]:
            starts=scan["STAR_STARTS"] if network=="star" else [None]
            for start in starts:
                label={"complete":"Complete graph","ring":"Ring graph","star":"Star graph"}.get(network,network)
                if start:
                    label+=", optimal arm initially at "+("the hub" if start=="center" else "a leaf")
                add("network",label,network=network,star_start=start,
                    repeat_count=c["REPEATS"]["STAR"] if network=="star" else c["REPEATS"]["MAIN"],
                    sweep_group="Network topology",sweep_x=label,sweep_label="Topology and starting node")
    if enabled["schedule"]:
        variants=[("Baseline decay",{})]+[(f"Stationary, Δ={gap:g}",{"family":"stationary","gap":gap,"force_pure":True}) for gap in scan["SCHEDULE_GAPS"]]
        for label,extra in variants:
            for xi in scan["XI"]:
                add("schedule",f"{label}, ξ={xi:g}",h=1,schedule="scaled",xi=xi,
                    sweep_group=label+" / schedule multiplier",sweep_x=xi,sweep_label="Schedule multiplier",**extra)
            if scan["INCLUDE_H_EQUALS_h"]:
                add("schedule",label+", H=h",h=1,schedule="fixed",fixed_H=1,**extra)
            for h in scan["H"]:
                add("schedule",f"{label}, h={h}",h=h,schedule="scaled",xi=1.0,
                    sweep_group=label+" / communication interval",sweep_x=h,sweep_label="Communication opportunity interval",**extra)
    if enabled["scale"]:
        for n in scan["AGENTS"]:
            add("scale",f"Fixed number of arms, n={n}",n=n,network="complete",center=0,
                sweep_group="Varying the number of agents at fixed K",sweep_x=n,sweep_label="Number of agents")
            K=scan["ARMS_PER_AGENT"]*n
            add("scale",f"Fixed number of sticky arms per agent, n={n}, K={K}",n=n,K=K,network="complete",center=0,
                sweep_group="Varying the number of agents at fixed K/n",sweep_x=n,sweep_label="Number of agents")
        for K in scan["ARMS"]:
            add("scale",f"Fixed number of agents, K={K}",K=K,network="complete",center=0,
                sweep_group="Varying the number of arms at fixed n",sweep_x=K,sweep_label="Number of arms")
    if enabled["public_bias"]:
        for n in scan["PUBLIC_BIAS_AGENTS"]:
            for family in ("exp","power"):
                add("public_bias",f"Shared decay ({'exponential' if family=='exp' else 'power-law'}), n={n}",n=n,network="complete",center=0,
                    family=family,power=scan["PUBLIC_BIAS_POWER"],force_pure=True,
                    sweep_group="Shared decay: "+("exponential" if family=="exp" else "power-law"),sweep_x=n,sweep_label="Number of agents")
    if enabled["random_instances"]:
        for index in range(scan["RANDOM_INSTANCES"]):
            add("random_instances",f"Random instance {index+1}",instance_kind="random",instance_index=index,
                repeat_count=c["REPEATS"]["RANDOM_PER_INSTANCE"])
    if not cases:
        raise ValueError("Enable at least one experiment group.")
    for case in cases:
        for key in ("n","K","T","h","repeat_count"):
            _positive_integer(case[key],case["label"]+"."+key)
        if not 0 < case["gap"] < ins["BASE_BEST"]:
            raise ValueError("Each gap in the sweep must lie in (0, BASE_BEST).")
        if not np.isfinite(case["xi"]) or case["xi"]<=0:
            raise ValueError("Each schedule parameter XI in the sweep must be finite and positive.")
        if not np.isfinite(case["beta"]) or case["beta"]<=1:
            raise ValueError("Each schedule parameter BETA must be finite and greater than 1.")
        if case["schedule"] not in ("scaled","fixed"):
            raise ValueError("Unknown schedule mode.")
        _positive_integer(case["fixed_H"],"fixed H")
        _positive_integer(case["plateau_L"],"plateau length")
        for field in ("exp_rate","power"):
            if not np.isfinite(case[field]) or case[field]<=0:
                raise ValueError(field+" must be finite and positive.")
        if case["star_start"] not in (None,"center","leaf"):
            raise ValueError("STAR_STARTS must contain only 'center' or 'leaf'.")
        make_network(case["n"],case["network"],com["CUSTOM_P"],case["center"])
        make_schedule(case["n"],case["K"],case["T"],case,c)
    return cases



def _arm_vector(value,K,dtype,name):
    if np.issubdtype(np.dtype(dtype),np.integer):
        raw=np.asarray(value,dtype=float)
        limits=np.iinfo(dtype)
        if (not np.all(np.isfinite(raw)) or np.any(raw!=np.floor(raw))
                or np.any(raw<limits.min) or np.any(raw>=int(limits.max)+1)):
            raise ValueError(f"{name} must contain representable integers. Fractional values cannot be truncated.")
    a=np.asarray(value,dtype=dtype)
    if a.ndim==0:
        # np.full(..., dtype=str) truncates 'exp' to 'e'. repeat preserves the string width.
        a=np.repeat(a.reshape(1),K)
    if a.shape!=(K,):
        raise ValueError(f"{name} must be a scalar or a one-dimensional sequence of length K={K}.")
    return np.ascontiguousarray(a)



def make_instance(case,c):
    K,n=case["K"],case["n"]
    p=c["INSTANCE"]
    # Separate parameter streams omit K, n, and T from the seed, so increasing K preserves the draws for existing arms.
    def parameter_rng(tag):
        return np.random.default_rng(np.random.SeedSequence(
            [c["SEED"],case["instance_index"],tag]))
    manual=p["MANUAL"] if case["group"] in ("basic","random_instances") else None
    kinds=np.full(K,FAMILY_IDS[case["family"]],np.int64)
    if p["ALLOW_MIXED_FAMILIES"] and not case["force_pure"]:
        pool=np.array([FAMILY_IDS[f] for f in p["MIXED_FAMILIES"]],np.int64)
        kinds=parameter_rng(917).choice(pool,K)
    # Determine the curve families before drawing their rates and amplitudes. Apply manual numeric overrides last.
    if manual is not None and manual["families"] is not None:
        families=_arm_vector(manual["families"],K,str,"families")
        if any(f not in FAMILY_IDS for f in families):
            raise ValueError("MANUAL.families contains an unknown curve family.")
        kinds=np.asarray([FAMILY_IDS[f] for f in families],np.int64)
    if case["platform_special"]:
        best,desired_best=0,0
    elif p["BEST_ARM"] is None:
        best=min(K,c["N_AGENTS"]+1)-1
        desired_best=min(K,n+1)-1
    else:
        _positive_integer(p["BEST_ARM"],"BEST_ARM")
        best=int(p["BEST_ARM"])-1
        desired_best=best
    if not 0<=best<K:
        raise ValueError("BEST_ARM is a 1-based index and must lie in 1..K. Use None for automatic scaling experiments.")
    if case["star_start"] is not None:
        owner=case["center"] if case["star_start"]=="center" else (case["center"]+1)%n
        candidates=[k for k in range(K) if k%n==owner and k>=2]
        if not candidates:
            raise ValueError("The designated starting node in the star graph has no sticky arm outside the initial low-index arms. Increase K or decrease n.")
        if p["BEST_ARM"] is not None:
            if best%n!=owner or best<2:
                raise ValueError("BEST_ARM conflicts with the starting node in the star graph. Use BEST_ARM=None for this sweep.")
        else:
            desired_best=candidates[0]
    bases=np.full(K,p["BASE_BEST"]-case["gap"],float)
    if case["instance_kind"]=="random":
        bases=p["BASE_BEST"]-parameter_rng(918).uniform(*p["RANDOM_GAP_RANGE"],K)
    bases[best]=p["BASE_BEST"]
    amps=np.full(K,p["AMPLITUDE"],float)
    multipliers=parameter_rng(919).uniform(*p["RATE_MULTIPLIER_RANGE"],K) if p["HETEROGENEOUS"] else np.ones(K)
    rates=np.where(kinds==1,case["exp_rate"],case["power"]).astype(float)*multipliers
    lengths=np.maximum(1,np.rint(case["plateau_L"]*multipliers)).astype(np.int64)
    amps[kinds==0]=0.0
    # CONFLICT_FRACTION is each eligible suboptimal arm's selection probability and hence the expected fraction before the fallback.
    # If no arm is selected, add one. This fallback and moving the canonical best arm are exceptions to prefix consistency for small K.
    if p["EARLY_LATE_CONFLICT"] and K>1 and np.any(kinds!=0):
        if kinds[best]!=0:
            amps[best]=p["BEST_AMPLITUDE"]
        eligible=(kinds!=0)
        eligible[best]=False
        draws=parameter_rng(920).random(K)
        selected=eligible & (draws<p["CONFLICT_FRACTION"])
        if np.any(eligible) and not np.any(selected):
            choices=np.flatnonzero(eligible)
            selected[choices[np.argmin(draws[choices])]]=True
        best_initial=bases[best]+amps[best]
        unselected=eligible & ~selected
        amps[unselected]=np.minimum(amps[unselected],np.maximum(0.,best_initial-bases[unselected]))
        amps[selected]=np.maximum(amps[selected],best_initial+p["INITIAL_ADVANTAGE"]-bases[selected])
    # When n or the starting node on the star graph changes, swap entire arm profiles to preserve the multiset of reward curves.
    if desired_best!=best:
        for vector in (bases,amps,rates,lengths,kinds):
            vector[[best,desired_best]]=vector[[desired_best,best]]
        best=desired_best
    # Use the paper's two-arm plateau counterexample in place of the generic instance.
    if case["platform_special"]:
        bases=np.array([.5,.25]); amps=np.array([0.,.5])
        kinds=np.array([0,3],np.int64); rates=np.ones(2)
        lengths=np.full(2,case["plateau_L"],np.int64); best=0
    # Manual settings apply only to baseline and random instances, so a manual limiting mean cannot override a prescribed gap sweep.
    if manual is not None:
        for name,key,dtype in (("bases","bases",float),("amplitudes","amps",float),
                                ("rates","rates",float),("plateau_lengths","lengths",np.int64)):
            if manual[name] is not None:
                arr=_arm_vector(manual[name],K,dtype,name)
                if key=="bases": bases=arr
                elif key=="amps": amps=arr
                elif key=="rates": rates=arr
                else: lengths=arr
        amps[kinds==0]=0.0
        best=int(np.argmax(bases))
    if not np.all(np.isfinite(bases)) or not np.all(np.isfinite(amps)) or not np.all(np.isfinite(rates)):
        raise ValueError("Arm parameters must all be finite.")
    if np.any(bases<=0) or np.any(amps<0) or np.any(bases+amps>1+1e-12) or np.any(rates<=0) or np.any(lengths<1):
        raise ValueError("Arm parameters must satisfy b > 0, a >= 0, b + a <= 1, rate > 0, and L >= 1. To reverse the initial and limiting rankings, a smaller amplitude or a lower optimal limiting mean may be necessary.")
    if np.count_nonzero(bases==bases.max())!=1:
        raise ValueError("A unique arm with the highest limiting mean is required.")
    result={"bases":np.ascontiguousarray(bases),"amps":np.ascontiguousarray(amps),
            "rates":np.ascontiguousarray(rates),"lengths":np.ascontiguousarray(lengths),
            "kinds":np.ascontiguousarray(kinds),"best_arm":best}
    result["initial_conflict_arms"]=np.flatnonzero(bases+amps>bases[best]+amps[best]+1e-12)
    result["actual_conflict_count"]=int(result["initial_conflict_arms"].size)
    result["manual_parameters_override_conflict"]=bool(manual is not None and any(
        manual[key] is not None for key in ("bases","amplitudes","rates","plateau_lengths","families")))
    return result



def _report_t95(count):
    """Return a conservative two-sided 95% t critical value using the next lower tabulated degrees of freedom, without SciPy."""
    df = int(count) - 1
    if df <= 0:
        return np.nan
    table = [
        12.706205, 4.302653, 3.182447, 2.776446, 2.570582,
        2.446912, 2.364625, 2.306005, 2.262158, 2.228139,
        2.200986, 2.178813, 2.160369, 2.144787, 2.131450,
        2.119906, 2.109816, 2.100923, 2.093025, 2.085964,
        2.079614, 2.073874, 2.068658, 2.063899, 2.059539,
        2.055530, 2.051831, 2.048408, 2.045230, 2.042273,
    ]
    if df <= 30:
        return table[df - 1]
    for threshold, value in [(120, 1.979931), (60, 2.000298), (40, 2.021076)]:
        if df >= threshold:
            return value
    return table[-1]



def _report_stats(values):
    """Return pointwise means, t-interval half-widths, and valid counts. One replicate gives no interval."""
    values = np.asarray(values, dtype=float)
    valid = np.isfinite(values)
    count = np.sum(valid, axis=0)
    total = np.sum(np.where(valid, values, 0.0), axis=0)
    mean = np.divide(total, count, out=np.full_like(total, np.nan), where=count > 0)
    squared = np.sum(np.where(valid, (values - mean) ** 2, 0.0), axis=0)
    variance = np.divide(squared, count - 1, out=np.full_like(total, np.nan), where=count > 1)
    critical = np.array([_report_t95(n) for n in np.asarray(count).ravel()]).reshape(count.shape)
    half = critical * np.sqrt(variance / np.maximum(count, 1))
    return mean, half, count



def _report_font(plot_config):
    """Check font coverage before running the experiment so all plot labels can be rendered."""
    import matplotlib
    from matplotlib import font_manager
    from matplotlib.ft2font import FT2Font

    font_path = plot_config.get("font_path")
    preferred = plot_config.get("font_family")
    required = set("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789Δαβδηλξ±")
    if font_path:
        path = Path(font_path).expanduser()
        if not path.is_file():
            raise FileNotFoundError("The specified font file does not exist: %s" % path)
        charmap = FT2Font(str(path)).get_charmap()
        missing = sorted(char for char in required if ord(char) not in charmap)
        if missing:
            raise RuntimeError("The specified font lacks required characters (e.g., %s): %s" % ("".join(missing[:8]), path))
        font_manager.fontManager.addfont(str(path))
        preferred = font_manager.FontProperties(fname=str(path)).get_name()
    available = {font.name for font in font_manager.fontManager.ttflist}
    candidates = ([preferred] if preferred else []) + [
        "Microsoft YaHei", "SimHei", "Noto Sans CJK SC", "Source Han Sans SC",
        "WenQuanYi Micro Hei", "SimSun", "Arial Unicode MS",
        "DejaVu Sans", "Arial", "Liberation Sans", "Noto Sans",
    ]
    selected = None
    for name in candidates:
        if name not in available:
            continue
        path = font_manager.findfont(font_manager.FontProperties(family=name), fallback_to_default=False)
        charmap = FT2Font(str(path)).get_charmap()
        if all(ord(char) in charmap for char in required):
            selected = name
            break
    if selected is None:
        raise RuntimeError(
            "No font covering the plot labels was found. Install DejaVu Sans, "
            "set OUTPUT['FONT_PATH'] to a suitable font file, or specify its name in PLOT_CONFIG['font_family']."
        )
    matplotlib.rcParams.update({
        "font.family": "sans-serif", "font.sans-serif": [selected],
        "axes.unicode_minus": False, "pdf.fonttype": 42, "ps.fonttype": 42,
        "axes.grid": True, "grid.alpha": 0.22, "font.size": 10,
        "legend.fontsize": 8, "figure.dpi": 110,
    })
    return selected



def _report_subplots(plot_config, nrows=1, ncols=1, figsize=(9.4, 5.7), **kwargs):
    """Render background plots on a separate Agg canvas while preserving the active Spyder or desktop pyplot backend."""
    if plot_config.get("show", False):
        import matplotlib.pyplot as plt
        return plt.subplots(nrows, ncols, figsize=figsize, **kwargs)
    from matplotlib.figure import Figure
    from matplotlib.backends.backend_agg import FigureCanvasAgg

    fig = Figure(figsize=figsize)
    FigureCanvasAgg(fig)
    return fig, fig.subplots(nrows=nrows, ncols=ncols, **kwargs)



def _report_save(fig, directory, filename, plot_config):
    """Save the PNG with notes on coincident means and the empirical parameter values used."""
    import textwrap
    if plot_config.get("only_bgosine_plots", False):
        label = plot_config.get("algorithm_labels", {}).get("bgosine", _REPORT_LABELS["bgosine"])
        own_labels = {label, label + " (lower bound)", label + " (upper bound)"}
        has_bgosine = any(name in own_labels and np.any(np.isfinite(y))
                          for ax in fig.axes for _, y, name in getattr(ax, "_report_curves", []))
        if not has_bgosine:
            if plot_config.get("show", False):
                import matplotlib.pyplot as plt
                plt.close(fig)
            else:
                fig.clear()
            return
    notes = list(plot_config.get("extra_notes", []))
    for index, ax in enumerate(fig.axes):
        prefix = ("Panel %d: " % (index + 1)) if len(fig.axes) > 1 else ""
        notes.extend(prefix + note for note in _report_overlap_notes(ax))
    legend_labels = [text for ax in fig.axes for text in ax.get_legend_handles_labels()[1]]
    if any("EFF-FEWA" in label for label in legend_labels):
        if any("Independent EFF-FEWA" in label for label in legend_labels):
            notes.append(plot_config.get("independent_eff_note", "Independent EFF-FEWA uses the parameters specified for this run."))
        if any("Centralized batched EFF-FEWA" in label for label in legend_labels):
            notes.append(plot_config.get("central_eff_note", "Centralized EFF-FEWA uses the parameters specified for this run."))
    if any("Cooperative EFF-FEWA" in label for label in legend_labels):
        notes.append(plot_config.get("cooperative_eff_note", "Cooperative and independent EFF-FEWA use the same window parameters."))
    if any("EFF-RAW-UCB" in label for label in legend_labels):
        notes.append(plot_config.get("raw_ucb_note", "Independent EFF-RAW-UCB uses geometrically spaced windows (m = 2)."))
    wrapped = [line for note in notes for line in textwrap.wrap(note, width=85)]
    if wrapped:
        old_width, old_height = fig.get_size_inches()
        footer = 0.20 * len(wrapped) + 0.12
        fig.set_size_inches(old_width, old_height + footer)
        fig.text(0.015, 0.012, "\n".join(wrapped), ha="left", va="bottom", fontsize=8)
        fig.tight_layout(rect=(0, footer / (old_height + footer), 1, 1))
    else:
        fig.tight_layout()
    if plot_config.get("save", True):
        directory = Path(directory)
        directory.mkdir(parents=True, exist_ok=True)
        filename = plot_config.get("filename_prefix", "") + filename
        fig.savefig(directory / (filename + ".png"), dpi=int(plot_config.get("dpi", 170)), bbox_inches="tight")
    if plot_config.get("show", False):
        import matplotlib.pyplot as plt
        plt.show(block=False)
    else:
        fig.clear()



def _report_series(result, metric, points):
    values = np.asarray(result[metric], dtype=float)
    if values.ndim == 0:
        if points != 1:
            raise ValueError("Metric %s requires a value at each checkpoint. Only the final value was supplied." % metric)
        values = values.reshape(1)
    if values.shape[0] != points:
        raise ValueError("The number of checkpoints for metric %s must match the length of times." % metric)
    if values.ndim == 2:
        # Sum communication and loss across nodes. Average fractions and biases across nodes.
        if metric in {"requests", "replies", "transmissions", "load", "bottom_loss",
                      "missing_node_rounds", "team_value", "realized_team",
                      "holding_bottom_loss", "plateau_extra_pulls", "reward_uploads",
                      "payload_bits", "total_messages"}:
            values = values.sum(axis=1)
        else:
            values = values.mean(axis=1)
    if values.ndim != 1:
        raise ValueError("Metric %s must be a one-dimensional time series or a two-dimensional (time, node) array." % metric)
    return values



def _report_stack(results, metric, points):
    if not all(metric in result for result in results):
        return None
    return np.stack([_report_series(result, metric, points) for result in results])



def _report_oracle(oracle, points, single=False):
    item = oracle.get("single") if single else oracle
    if item is None:
        return None
    lo = np.broadcast_to(np.asarray(item["lo"], dtype=float), (points,))
    hi = np.broadcast_to(np.asarray(item["hi"], dtype=float), (points,))
    if np.any(lo > hi + 1e-8):
        raise ValueError("The lower bound on the optimal value cannot exceed the upper bound.")
    if item.get("exact", False) and not np.allclose(lo, hi, rtol=1e-10, atol=1e-8):
        raise ValueError("The bounds lo and hi must agree for an exact oracle.")
    return dict(lo=lo, hi=hi, exact=bool(item.get("exact", False)),
                label=str(item.get("label", "Optimal benchmark")), n=int(item.get("n", 1)))



def _report_band(ax, times, values, label, color, divisor=1.0, algorithm=None):
    mean, half, count = _report_stats(values / divisor)
    if ax is not None:
        style = _report_style(algorithm)
        style.pop("marker")
        style["color"] = color
        ax.plot(times, mean, label=label, linewidth=1.5, **style)
        _report_register_curve(ax, times, mean, label)
        if np.any(count > 1):
            ax.fill_between(times, mean - half, mean + half, color=color, alpha=0.15)
    return mean, half, count



def _report_style(name):
    """Keep styles consistent across algorithm orderings, subsets, and plot types."""
    styles = {
        "bgosine": ("#0072B2", "-", "o"),
        "full_ucb": ("#D55E00", "--", "s"),
        "independent_fewa": ("#009E73", "-.", "^"),
        "eff_fewa": ("#009E73", "-.", "^"),
        "fewa": ("#009E73", ":", "v"),
        "no_comm": ("#CC79A7", ":", "D"),
        "coop_eff_fewa": ("#0095B6", "--", "p"),
        "eff_raw_ucb": ("#8F3985", "-.", "<"),
        "random_rec": ("#B87800", ":", ">"),
        "single_dcto": ("#6F4C9B", "-.", "P"),
        "single_ucb": ("#E69F00", "--", "X"),
        "central_fewa": ("#5C6B73", "--", "h"),
        "centralized_fewa": ("#5C6B73", "--", "h"),
    }
    color, line, marker = styles.get(name, ("#333333", "-", "o"))
    return {"color": color, "linestyle": line, "marker": marker}



def _report_register_curve(ax, x, y, label):
    """Record the plotted means to identify overlapping curves without changing the curves or intervals."""
    curves = getattr(ax, "_report_curves", [])
    curves.append((np.asarray(x), np.asarray(y, dtype=float), str(label)))
    ax._report_curves = curves



def _report_overlap_notes(ax):
    curves = getattr(ax, "_report_curves", [])
    used, notes = set(), []
    for i, (x, y, label) in enumerate(curves):
        if i in used or not np.any(np.isfinite(y)):
            continue
        matches = [label]
        for j in range(i + 1, len(curves)):
            xx, yy, other = curves[j]
            if j not in used and np.array_equal(x, xx) and y.shape == yy.shape and np.allclose(
                    y, yy, rtol=1e-12, atol=1e-10, equal_nan=True):
                matches.append(other)
                used.add(j)
        if len(matches) > 1:
            notes.append("Coincident mean curves: " + " = ".join(matches))
    return notes



def _paired_seeds(c,case,repeat):
    # Exclude lambda and the algorithm so each replicate shares the same reward stream by round and agent.
    # Exclude the number of replicates and workers so adding either preserves existing trajectories.
    case_seed=int(_digest(_legacy_hash_fields({k:v for k,v in case.items() if k not in ("repeat_count","case_id")}),8),16)
    values=np.random.SeedSequence([c["SEED"],case_seed,repeat]).generate_state(2,dtype=np.uint64)
    return values[0],values[1]



def _prewarm(c):
    """Compile on the main thread in a dozen rounds to avoid contention among eight workers during JIT compilation."""
    tiny=copy.deepcopy(c)
    tiny.update(N_AGENTS=2,N_ARMS=3,HORIZON=12,QUICK_CHECK=False)
    tiny["GROUPS"]={key:key=="basic" for key in c["GROUPS"]}
    tiny["INSTANCE"]["BEST_ARM"]=None
    tiny["INSTANCE"]["MANUAL"]={k:None for k in tiny["INSTANCE"]["MANUAL"]}
    tiny["COMMUNICATION"].update(NETWORK="complete",H=1,SCHEDULE="fixed",FIXED_H=2,STAR_CENTER=0)
    tiny["WINDOW"]["EXACT_FEWA_MAX_T"]=max(12,tiny["WINDOW"]["EXACT_FEWA_MAX_T"])
    case=build_cases(tiny)[0]
    instance=make_instance(case,tiny)
    times=np.arange(13,dtype=np.int64)
    for name in ("bgosine","eff_fewa","fewa","central_fewa","random_rec","coop_eff_fewa","eff_raw_ucb"):
        if c["ALGORITHMS"].get(name, False) and (name != "central_fewa" or c["RUN_LAMBDA_1"]):
            simulate_algorithm(name,case,instance,1,times,np.uint64(12),np.uint64(22),tiny)



def _compact_plot_stems(case, cases, fatigue, extra_basic_plots=()):
    """Select representative cases using only prespecified parameters, independently of the results."""
    stems = set()
    group = case["group"]
    peers = [item for item in cases if item["group"] == group]
    main_cases = [item for item in cases if item["group"] == "basic"] or cases[:1]
    if case["case_id"] in {item["case_id"] for item in main_cases}:
        stems.update(("01_per_agent_cumulative_pseudo_regret", "02_paired_reward_difference", "06_optimal_arm_availability_and_selection"))
        stems.update(_LEGACY_PLOT_STEMS.get(stem, stem) for stem in extra_basic_plots)
    if case["case_id"] == cases[0]["case_id"]:
        stems.add("04_single_agent_cumulative_pseudo_regret")
    if group == "random_instances" or case.get("instance_kind") == "random":
        stems.add("02_paired_reward_difference")
    if group == "plateau":
        peers = [item for item in peers if item.get("sweep_group") == case.get("sweep_group")]
        representative = max(peers, key=lambda item: (item["T"], item["plateau_L"]))
        if case["case_id"] == representative["case_id"]:
            stems.update(("01_per_agent_cumulative_pseudo_regret", "13_extra_pulls_after_plateau"))
    elif group == "network":
        # Keep one load plot per starting position on the star, or use the last configured network if no star is included.
        stars = [item for item in peers if item["network"] == "star"]
        selected = stars or peers[-1:]
        if case["case_id"] in {item["case_id"] for item in selected}:
            stems.add("11_communication_load_per_node")
    elif group in ("schedule", "scale"):
        key = (lambda item: (item["h"], item["xi"])) if group == "schedule" else (lambda item: (item["n"], item["K"]))
        if case["case_id"] == max(peers, key=key)["case_id"]:
            stems.add("08_communication_overhead")
    elif group == "public_bias" and fatigue == 1:
        peers = [item for item in peers if item["family"] == case["family"]]
        if case["case_id"] == max(peers, key=lambda item: item["n"])["case_id"]:
            stems.add("09_shared_decay_bias")
    return stems



def _picture_name_text(value):
    """Keep parameter descriptions in filenames and remove characters that Windows disallows."""
    text = str(value)
    for old, new in (("K/n", "arms_per_agent"),
                     ("Δ=", "gap_"), ("η=", "exponential_rate_"), ("α=", "power_law_exponent_"),
                     ("ξ=", "schedule_factor_"), ("H=h", "period_equals_communication_interval"),
                     ("n=", "agents_"), ("K=", "arms_"), ("T=", "horizon_"),
                     ("L=", "plateau_length_"), ("h=", "communication_interval_")):
        text = text.replace(old, new)
    return "".join("_" if char in '<>:"/\\|?*' or ord(char) < 32 else char
                   for char in text).strip(" .")[:70]



def _case_picture_prefix(case_number, case, fatigue):
    groups = {"basic": "Baseline performance", "small_gap": "Small-gap experiments", "plateau": "Plateau stress test",
              "decay": "Decay parameters", "network": "Network topology", "schedule": "Communication schedule",
              "scale": "Agent and arm counts", "public_bias": "Shared decay mechanism", "random_instances": "Random instances"}
    group = groups.get(case["group"], case["group"])
    label = _picture_name_text(case["label"])
    mechanism = "Individual decay" if fatigue == 0 else "Shared decay"
    detail = "" if label == group else label + "_"
    return f"{case_number:03d}_{group}_{mechanism}_{detail}"



def report_case(case_dir, case_meta, algorithm_results, oracle, plot_config=None):
    """Plot the selected metrics for matching replicate IDs. Unused metrics may be omitted."""
    config = {} if plot_config is None else dict(plot_config)
    plots_enabled = config.get("save", True) or config.get("show", False)
    selected_stems = config.get("selected_stems")
    if selected_stems is not None:
        selected_stems = {_LEGACY_PLOT_STEMS.get(stem, stem) for stem in selected_stems}
    def want_plot(stem):
        return plots_enabled and (selected_stems is None or stem in selected_stems)
    if not plots_enabled or selected_stems == set():
        return
    directory = Path(case_dir)
    directory.mkdir(parents=True, exist_ok=True)
    _report_font(config)
    if not algorithm_results:
        raise ValueError("No algorithm results are available to report.")
    if any(not results for results in algorithm_results.values()):
        raise ValueError("The result list for each algorithm must be nonempty.")
    first = next(iter(algorithm_results.values()))[0]
    times = np.asarray(first["times"], dtype=np.int64)
    if times.ndim != 1 or times.size == 0 or np.any(np.diff(times) <= 0):
        raise ValueError("times must be a nonempty, strictly increasing one-dimensional array.")
    for name, results in algorithm_results.items():
        for result in results:
            if not np.array_equal(times, result["times"]):
                raise ValueError("Algorithm %s uses different checkpoint times and cannot be compared pointwise." % name)
    points = len(times)
    labels = dict(_REPORT_LABELS, **config.get("algorithm_labels", {}))
    names = list(algorithm_results)
    colors = {name: _report_style(name)["color"] for name in names}
    n = int(case_meta["n"])
    team_names = names
    title = str(case_meta.get("title", case_meta.get("case_id", "Experiment")))
    if config.get("quick_check", False):
        title = "Quick check (preliminary results): n=%s, K=%s, T=%s" % (
            case_meta["n"], case_meta.get("K", "?"), case_meta.get("T", int(times[-1])))
        if case_meta.get("group") == "plateau":
            title += ", actual L=%s" % case_meta.get("plateau_L", "unrecorded")
    if case_meta.get("group") == "plateau":
        title += "\nPlateau stress test: adaptation after the transient plateau ends"
    completed = len(next(iter(algorithm_results.values())))
    target = int(case_meta.get("repeat_count", completed))
    if case_meta.get("instance_kind") == "random" or completed < target:
        title += "\nCompleted %d/%d paired replicates%s" % (completed, target, " (partial results)" if completed < target else "")
    # Keep the original replicate order for each curve, independent of thread completion order.
    reference_ids = [int(r.get("repeat", i)) for i, r in enumerate(next(iter(algorithm_results.values())))]
    for name, results in algorithm_results.items():
        ids = [int(r.get("repeat", i)) for i, r in enumerate(results)]
        if ids != reference_ids:
            raise ValueError("Replicate IDs do not match for algorithm %s." % name)
    need_regret = any(want_plot(stem) for stem in REGRET_PLOTS)
    values = {}
    team_oracle = None
    if need_regret:
        if oracle is None:
            raise ValueError("Regret plots require the corresponding oracle.")
        values = {name: _report_stack(algorithm_results[name], "team_value", points) for name in names}
        if any(value is None for value in values.values()):
            raise ValueError("Each replicate must record team_value for the regret plots.")
        team_oracle = _report_oracle(oracle, points)
        if team_oracle["n"] != n:
            raise ValueError("The number of agents in the team oracle must match the number in the scenario.")

    def draw_regret(group, reference, divisor, stem, ylabel):
        if not want_plot(stem) or not group or reference is None:
            return
        fig, ax = _report_subplots(config, figsize=(9.4, 5.7))
        for name in group:
            avg, half, count = _report_stats(values[name] / divisor)
            lower_samples = reference["lo"] / divisor - values[name] / divisor
            if not reference["exact"]:
                lower_samples = np.maximum(0.0, lower_samples)
            low, lower_half, _ = _report_stats(lower_samples)
            high = reference["hi"] / divisor - avg
            color, label = colors[name], labels.get(name, name)
            if reference["exact"]:
                ax.plot(times, low, color=color, linestyle=_report_style(name)["linestyle"], label=label, linewidth=1.5)
                _report_register_curve(ax, times, low, label)
                if np.any(count > 1):
                    ax.fill_between(times, low - half, low + half, color=color, alpha=0.15)
            else:
                ax.plot(times, low, color=color, linestyle=_report_style(name)["linestyle"], linewidth=1.3, label=label + " (regret bounds)")
                ax.plot(times, high, color=color, linestyle=_report_style(name)["linestyle"], linewidth=1.3)
                _report_register_curve(ax, times, low, label + " (lower bound)")
                _report_register_curve(ax, times, high, label + " (upper bound)")
                ax.fill_between(times, low, high, color=color, alpha=0.12)
                if np.any(count > 1):
                    ax.plot(times, np.maximum(0.0, low - lower_half), color=color,
                            linestyle=":", linewidth=0.7)
                    ax.plot(times, high + half, color=color, linestyle=":", linewidth=0.7)
        note = ("Shading shows pointwise 95% t confidence intervals for the mean" if reference["exact"] else
                "Shading shows expected regret bounds\nDotted lines show the outer endpoints of pointwise 95% t intervals")
        ax.set(title=title + "\n" + note, xlabel="Round", ylabel=ylabel)
        ax.legend()
        _report_save(fig, directory, stem, config)

    # When an ablation plot is available, show the two recommendation variants there.
    ablations = [name for name in ("bgosine", "random_rec", "no_comm") if name in team_names]
    primary = team_names
    if want_plot("15_recommendation_ablation") and len(ablations) >= 2:
        primary = [name for name in team_names if name not in ("random_rec", "no_comm")] or team_names
        draw_regret(ablations, team_oracle, n, "15_recommendation_ablation", "Cumulative pseudo-regret per agent")
    draw_regret(primary, team_oracle, n, "01_per_agent_cumulative_pseudo_regret", "Cumulative pseudo-regret per agent")
    draw_regret(team_names, team_oracle, 1, "03_team_cumulative_pseudo_regret", "Team cumulative pseudo-regret")

    def draw_metrics(metrics, stem, group=team_names):
        if not want_plot(stem):
            return
        usable = [(key, label, divisor) for key, label, divisor in metrics
                  if any(all(key in r for r in algorithm_results[name]) for name in group)]
        if not usable:
            return
        fig, axes = _report_subplots(config, len(usable), 1, figsize=(9.4, 3.7 * len(usable)), squeeze=False)
        for ax, (key, ylabel, divisor) in zip(axes[:, 0], usable):
            for name in group:
                stack = _report_stack(algorithm_results[name], key, points)
                if stack is not None:
                    _report_band(ax, times, stack, labels.get(name, name), colors[name], divisor, algorithm=name)
            ax.set(xlabel="Round", ylabel=ylabel)
            ax.legend()
        axes[0, 0].set_title(title + "\nShading shows pointwise 95% t confidence intervals for the mean")
        _report_save(fig, directory, stem, config)

    draw_metrics([("bottom_loss", "Cumulative limiting-mean loss\nper agent", n)], "05_limiting_mean_loss")
    draw_metrics([("holding_fraction", "Fraction of agents holding the arm\nwith the highest limiting mean", 1),
                  ("selection_fraction", "Fraction of pulls of the arm\nwith the highest limiting mean", 1),
                  ("recent_selection_fraction", "Recent pull fraction for the arm\nwith the highest limiting mean", 1),
                  ("missing_node_rounds", "Agent-rounds without access to the arm\nwith the highest limiting mean", 1)], "06_optimal_arm_availability_and_selection")
    draw_metrics([("holding_bottom_loss", "Cumulative limiting-mean loss per agent\nwhile holding the arm with the\nhighest limiting mean", n)], "12_selection_loss_when_optimal_arm_available")
    draw_metrics([("plateau_extra_pulls", "Cumulative team pulls of suboptimal\nplateau arms after their means drop", 1)], "13_extra_pulls_after_plateau")
    draw_metrics([("recommendation_accuracy", "Recommendation accuracy", 1)], "07_recommendation_accuracy",
                 group=[name for name in team_names if name in RECOMMENDING_ALGORITHMS])
    comm_metrics = [("requests", "Cumulative requests sent\nby the team", 1),
                    ("replies", "Cumulative replies sent\nby the team", 1),
                    ("transmissions", "Cumulative arm IDs transmitted\nby the team", 1)]
    if not any("transmissions" in result for results in algorithm_results.values() for result in results):
        comm_metrics[-1] = ("load", "Cumulative team transmissions\n(units specified in configuration)", 1)
    comm_metrics.append(("reward_uploads", "Cumulative reward values uploaded\nto the central controller", 1))
    draw_metrics(comm_metrics, "08_communication_overhead")
    draw_metrics([("payload_bits", "Arm-ID payload (bits)", 1),
                  ("total_messages", "Total request and reply messages", 1)], "14_message_count_and_payload_bits")
    draw_metrics([("current_bias", "Current decay bias", 1),
                  ("history_bias", "Mean decay bias over\nindividual pull histories", 1)], "09_shared_decay_bias")
    draw_metrics([("team_value", "Cumulative conditional expected\nreward per agent", n)], "10_cumulative_expected_reward")

    if want_plot("11_communication_load_per_node"):
        node_metrics = [("requests", "Requests sent per node\nby the final round"),
                        ("replies", "Replies sent per node\nby the final round"),
                        ("transmissions", "Arm IDs transmitted per node\nby the final round")]
        node_data = {}
        for name in team_names:
            for key, ylabel in node_metrics:
                results = algorithm_results[name]
                if all(key in r and np.asarray(r[key]).ndim == 2 for r in results):
                    array = np.stack([np.asarray(r[key], dtype=float)[-1] for r in results])
                    mean, half, count = _report_stats(array)
                    node_data[(name, key)] = (mean, half)
    if want_plot("11_communication_load_per_node") and node_data:
        fig, axes = _report_subplots(config, 3, 1, figsize=(9.4, 10.8))
        for ax, (key, ylabel) in zip(axes, node_metrics):
            for name in team_names:
                if (name, key) in node_data:
                    mean, half = node_data[(name, key)]
                    ax.errorbar(np.arange(1, len(mean) + 1), mean, yerr=half, color=colors[name],
                                marker=_report_style(name)["marker"], linestyle=_report_style(name)["linestyle"],
                                linewidth=1, label=labels.get(name, name))
                    _report_register_curve(ax, np.arange(1, len(mean) + 1), mean, labels.get(name, name))
            ax.set(xlabel="Node ID", ylabel=ylabel)
            ax.legend()
        axes[0].set_title(title + "\nCommunication load per node (error bars show pointwise 95% t confidence intervals)")
        _report_save(fig, directory, "11_communication_load_per_node", config)



def _algorithm_self_check(config=None):
    """Check the oracle, windows, synchronous rewards, degenerate cases, and reproducibility across threads."""
    c=copy.deepcopy(CONFIG if config is None else config)
    oracle_self_check()
    selfcheck_windows()
    c.update(N_AGENTS=2,N_ARMS=2,HORIZON=60,QUICK_CHECK=False)
    c["GROUPS"]={key:key=="basic" for key in c["GROUPS"]}
    c["INSTANCE"].update(BEST_ARM=None,ALLOW_MIXED_FAMILIES=False)
    c["INSTANCE"]["MANUAL"]={key:None for key in c["INSTANCE"]["MANUAL"]}
    c["COMMUNICATION"].update(NETWORK="complete",STAR_CENTER=0,H=1,SCHEDULE="fixed",FIXED_H=3)
    c["WINDOW"]["EXACT_FEWA_MAX_T"]=max(60,c["WINDOW"]["EXACT_FEWA_MAX_T"])
    case=build_cases(c)[0]; instance=make_instance(case,c)
    times=np.arange(61,dtype=np.int64)
    for lam in (0,1):
        a=simulate_algorithm("bgosine",case,instance,lam,times,123,456,c)
        b=simulate_algorithm("full_ucb",case,instance,lam,times,123,456,c)
        assert np.array_equal(a["team_value"],b["team_value"]),"With K=2, the active set should always contain all arms."
        assert np.array_equal(a["final_counts"],b["final_counts"])
        for name in ("eff_fewa","fewa"):
            z=simulate_algorithm(name,case,instance,lam,times,123,456,c)
            assert z["final_counts"].sum()==120
    # With no decay and one agent, the two endpoints should agree. Synchronization should also hold with one arm.
    one=dict(case,n=1,network="complete")
    x=simulate_algorithm("full_ucb",one,instance,0,times,1,2,c)
    y=simulate_algorithm("full_ucb",one,instance,1,times,1,2,c)
    assert np.allclose(x["team_value"],y["team_value"],rtol=0,atol=1e-12)
    with ThreadPoolExecutor(max_workers=2) as pool:
        parallel=list(pool.map(lambda _:simulate_algorithm("eff_fewa",case,instance,1,times,123,456,c),range(2)))
    assert np.array_equal(parallel[0]["team_value"],parallel[1]["team_value"])
    assert np.array_equal(parallel[0]["final_counts"],parallel[1]["final_counts"])
    # The default schedule should communicate before the terminal round and never at the end of T.
    tmp=dict(case,T=12,fixed_H=3,beta=2)
    assert np.array_equal(make_schedule(2,2,12,tmp,c)[2],np.array([3]))
    return "Self-checks passed for the oracle, windows, synchronous special cases, terminal communication, and parallel reproducibility. D-CTO comparisons follow the algorithm settings."



# ==================== Schedule computation by plot (PNG output only) ====================
PLOT_METRICS = {
    "01_per_agent_cumulative_pseudo_regret": ("team_value",),
    "03_team_cumulative_pseudo_regret": ("team_value",),
    "05_limiting_mean_loss": ("bottom_loss",),
    "06_optimal_arm_availability_and_selection": ("holding_fraction", "selection_fraction",
                          "recent_selection_fraction", "missing_node_rounds"),
    "07_recommendation_accuracy": ("recommendation_accuracy",),
    "08_communication_overhead": ("requests", "replies", "transmissions", "reward_uploads"),
    "09_shared_decay_bias": ("current_bias", "history_bias"),
    "10_cumulative_expected_reward": ("team_value",),
    "11_communication_load_per_node": ("requests", "replies", "transmissions"),
    "12_selection_loss_when_optimal_arm_available": ("holding_bottom_loss",),
    "13_extra_pulls_after_plateau": ("plateau_extra_pulls",),
    "14_message_count_and_payload_bits": ("payload_bits", "total_messages"),
    "15_recommendation_ablation": ("team_value",),
}
# Accept figure selections saved in earlier configuration files.
_LEGACY_PLOT_STEMS = {
    '01_\u4eba\u5747\u7d2f\u8ba1\u4f2a\u9057\u61be': '01_per_agent_cumulative_pseudo_regret',
    '02_\u5408\u4f5c\u914d\u5bf9\u6536\u76ca\u5dee': '02_paired_reward_difference',
    '03_\u56e2\u961f\u7d2f\u8ba1\u4f2a\u9057\u61be': '03_team_cumulative_pseudo_regret',
    '04_\u5355\u4eba\u7b97\u6cd5\u7d2f\u8ba1\u4f2a\u9057\u61be': '04_single_agent_cumulative_pseudo_regret',
    '05_\u5e95\u503c\u635f\u5931': '05_limiting_mean_loss',
    '06_\u6700\u4f18\u81c2\u6301\u6709\u4e0e\u9009\u62e9': '06_optimal_arm_availability_and_selection',
    '07_\u63a8\u8350\u6b63\u786e\u7387': '07_recommendation_accuracy',
    '08_\u901a\u4fe1\u5f00\u9500': '08_communication_overhead',
    '09_\u516c\u5171\u75b2\u52b3\u504f\u5dee': '09_shared_decay_bias',
    '10_\u7d2f\u8ba1\u671f\u671b\u6536\u76ca': '10_cumulative_expected_reward',
    '11_\u6bcf\u8282\u70b9\u901a\u4fe1\u8d1f\u8f7d': '11_communication_load_per_node',
    '12_\u6301\u6709\u6700\u4f18\u81c2\u65f6\u7684\u9009\u62e9\u635f\u5931': '12_selection_loss_when_optimal_arm_available',
    '13_\u5e73\u53f0\u7ed3\u675f\u540e\u7684\u989d\u5916\u62c9\u53d6': '13_extra_pulls_after_plateau',
    '14_\u6d88\u606f\u6570\u4e0e\u6bd4\u7279\u8f7d\u8377': '14_message_count_and_payload_bits',
    '15_\u63a8\u8350\u673a\u5236\u6d88\u878d': '15_recommendation_ablation',
}
REGRET_PLOTS = frozenset(("01_per_agent_cumulative_pseudo_regret", "03_team_cumulative_pseudo_regret", "15_recommendation_ablation"))
RECOMMENDING_ALGORITHMS = frozenset(("bgosine", "coop_eff_fewa", "random_rec"))
COMMUNICATION_METRICS = frozenset(("requests", "replies", "transmissions",
                                 "reward_uploads", "payload_bits", "total_messages"))


def build_plot_plan(c):
    """Select plots from the full case list before filtering to preserve case fields, numbers, and seeds."""
    cases = build_cases(c)
    plan = []
    experiments = c.get("EXPERIMENTS", {})
    ins = c["INSTANCE"]
    basic_covers_rate = (c["GROUPS"]["basic"] and ins["FAMILY"] == "exp"
                         and not ins["ALLOW_MIXED_FAMILIES"]
                         and all(value is None for value in ins["MANUAL"].values()))
    for case_number, case in enumerate(cases, 1):
        for fatigue, switch in ((0, "RUN_LAMBDA_0"), (1, "RUN_LAMBDA_1")):
            if not c[switch] or (case["platform_special"] and fatigue == 1):
                continue
            peers = [item for item in cases if fatigue == 0 or not item["platform_special"]]
            stems = _compact_plot_stems(case, peers, fatigue,
                                        c["OUTPUT"]["EXTRA_BASIC_PLOTS"]) & PLOT_METRICS.keys()
            algorithms = [name for name, on in c["ALGORITHMS"].items()
                          if on and (name != "central_fewa" or fatigue == 1)]
            if case["group"] == "basic" and sum(name in algorithms for name in ("bgosine", "random_rec", "no_comm")) >= 2:
                stems.add("15_recommendation_ablation")
            if case["group"] == "decay" and case["family"] == "exp" and experiments.get("RATE_REGRET", False):
                if not basic_covers_rate or case["exp_rate"] != ins["EXP_RATE"]:
                    stems.add("01_per_agent_cumulative_pseudo_regret")
            if case["group"] == "network" and experiments.get("NETWORK_REGRET", False):
                stems.add("01_per_agent_cumulative_pseudo_regret")
                stems.add("06_optimal_arm_availability_and_selection")
            if "07_recommendation_accuracy" in stems and (not RECOMMENDING_ALGORITHMS.intersection(algorithms)
                    or case["n"] == 1 or not len(make_schedule(case["n"], case["K"], case["T"], case, c)[2])):
                stems.remove("07_recommendation_accuracy")
            if not algorithms or not stems:
                continue
            metrics = frozenset(key for stem in stems for key in PLOT_METRICS[stem])
            communication_only = metrics <= COMMUNICATION_METRICS
            if not communication_only and c["OUTPUT"].get("SAVE_ENDPOINT_CSV", False):
                metrics = metrics.union(("team_value", "first_90pct_hold_time"))
            if not communication_only and ("fewa" in algorithms or
                    ("central_fewa" in algorithms and c["WINDOW"]["CENTRAL_ENGINE"] == "fewa")):
                if case["T"] > c["WINDOW"]["EXACT_FEWA_MAX_T"]:
                    raise ValueError(case["label"] + " exceeds the horizon limit for exact FEWA.")
            plan.append(dict(case_number=case_number, case=case, fatigue=fatigue,
                             algorithms=algorithms, stems=stems, metrics=metrics,
                             communication_only=communication_only))
    if not plan:
        raise ValueError("No plots are selected. Enable at least one experiment group that produces a selected plot.")
    return cases, plan


def _plot_settings(c):
    out, window = c["OUTPUT"], c["WINDOW"]
    labels = {"central_fewa": "Centralized batched FEWA"} if window["CENTRAL_ENGINE"] == "fewa" else {}
    def parameter_note(label, algorithm):
        values = _window_parameters(c, algorithm)
        return ("%s parameters: alpha=%g, delta0=%g, includeK=%s, sigma2=%g." % (
            label, values["ALPHA"], values["DELTA0"], values["INCLUDE_K"], values["SIGMA2"]))
    return dict(save=out["SAVE_PLOTS"], show=out["SHOW_PLOTS"],
                only_bgosine_plots=out.get("ONLY_BGOSINE_PLOTS", False), dpi=out["DPI"], font_path=out["FONT_PATH"],
                algorithm_labels=labels, quick_check=c["QUICK_CHECK"],
                independent_eff_note=parameter_note("Independent EFF-FEWA", "eff_fewa"),
                cooperative_eff_note=parameter_note("Cooperative EFF-FEWA", "coop_eff_fewa"),
                raw_ucb_note=parameter_note("Independent EFF-RAW-UCB (m=2)", "eff_raw_ucb"),
                central_eff_note=parameter_note("Centralized EFF-FEWA", "central_fewa")
                    + " The variance proxy for the batch mean is divided by the number of agents.")


def _plot_oracle(unit, c):
    if not unit["stems"] & REGRET_PLOTS:
        return None
    setting, instance, case = c["ORACLE"], unit["instance"], unit["case"]
    lo, hi, metadata = compute_oracle(
        *[instance[key] for key in ("bases", "amps", "rates", "lengths", "kinds")],
        case["n"], unit["times"], unit["fatigue"], mode=setting["PUBLIC_MODE"],
        max_states=setting["MAX_STATES"], max_transitions=setting["MAX_TRANSITIONS"],
        max_seconds=setting["MAX_SECONDS"])
    return dict(lo=lo, hi=hi, n=case["n"], exact=metadata["exact"], label=metadata["label"])


def _calculate_plot_sample(unit, algorithm, repeat, c):
    case, times = unit["case"], unit["times"]
    reward_seed, comm_seed = _paired_seeds(c, case, repeat)
    if unit["communication_only"]:
        result = simulate_communication(algorithm, case, times, comm_seed, c, unit["prepared"])
        result = {key: value for key, value in result.items()
                  if key in unit["metrics"] or key in ("times", "n", "H")}
    else:
        result = simulate_algorithm(algorithm, case, unit["instance"], unit["fatigue"],
                                    times, reward_seed, comm_seed, c,
                                    required_metrics=unit["metrics"], prepared=unit["prepared"])
        # Validate in memory using only the oracle and diagnostics already required.
        oracle = unit["oracle"]
        if oracle is not None:
            value = result["team_value"]
            if (not np.all(np.isfinite(value)) or np.any(np.diff(value) < -1e-8)
                    or np.any(value < -1e-8)
                    or np.any(value > oracle["hi"] + max(1e-7, case["n"] * case["T"] * 2e-10))):
                raise AssertionError("The reward trajectory failed the oracle consistency check.")
        result.pop("final_counts", None)
    result["repeat"] = repeat
    return result


def _choose_workers(c, plan):
    """Time identical workloads using a short benchmark that leaves experiment seeds and samples unchanged."""
    requested = c["EXECUTION"]["WORKERS"]
    if requested != "auto":
        return int(requested)
    logical = os.cpu_count() or 1
    units = [unit for unit in plan if not unit["communication_only"]]
    if c["QUICK_CHECK"] or not units:
        return min(8, logical)
    candidates = sorted({max(1, logical // 2), max(1, 3 * logical // 4), logical})
    if len(candidates) == 1:
        return candidates[0]
    unit = max(units, key=lambda item: item["case"]["n"] * item["case"]["K"])
    case = dict(unit["case"], T=min(unit["case"]["T"], 10000))
    prepared = prepare_simulation(case, c)
    times = make_checkpoints(case["T"], c)
    algorithms = [name for name in ("eff_raw_ucb", "eff_fewa", "coop_eff_fewa", "full_ucb", "bgosine")
                  if name in unit["algorithms"]]
    if not algorithms:
        algorithms = unit["algorithms"][:1]
    jobs = [algorithms[i % len(algorithms)] for i in range(max(12, 2 * logical))]
    def probe(name):
        simulate_algorithm(name, case, unit["instance"], unit["fatigue"], times,
                           np.uint64(123), np.uint64(456), c,
                           required_metrics=unit["metrics"], prepared=prepared)
    for name in algorithms:
        probe(name)
    measurements = {workers: [] for workers in candidates}
    print("Benchmarking parallel throughput (excluded from experiment replicates)...", flush=True)
    for order in (candidates, candidates[::-1]):
        for workers in order:
            with ThreadPoolExecutor(max_workers=workers) as pool:
                started = time.perf_counter()
                list(pool.map(probe, jobs))
                measurements[workers].append(time.perf_counter() - started)
    medians = {workers: float(np.median(values)) for workers, values in measurements.items()}
    selected = min(medians, key=medians.get)
    print("Parallel benchmark: " + ", ".join(f"{workers} threads: {seconds:.2f} s" for workers, seconds in medians.items())
          + f". Using {selected} worker threads.", flush=True)
    return selected


def self_check(config=None):
    c = copy.deepcopy(CONFIG if config is None else config)
    _algorithm_self_check(c)
    c.update(N_AGENTS=4, N_ARMS=7, HORIZON=80, QUICK_CHECK=False)
    c["WINDOW"]["EXACT_FEWA_MAX_T"] = max(80, c["WINDOW"]["EXACT_FEWA_MAX_T"])
    c["GROUPS"] = {key: key == "basic" for key in c["GROUPS"]}
    c["INSTANCE"].update(BEST_ARM=None, ALLOW_MIXED_FAMILIES=False)
    c["INSTANCE"]["MANUAL"] = {key: None for key in c["INSTANCE"]["MANUAL"]}
    c["COMMUNICATION"].update(NETWORK="star", STAR_CENTER=0, H=1, SCHEDULE="fixed", FIXED_H=2)
    case = build_cases(c)[0]
    instance, times = make_instance(case, c), make_checkpoints(case["T"], c)
    prepared = prepare_simulation(case, c)
    metrics = frozenset(key for values in PLOT_METRICS.values() for key in values)
    for fatigue in (0, 1):
        for algorithm in ("bgosine", "full_ucb", "no_comm", "eff_fewa", "central_fewa",
                          "coop_eff_fewa", "eff_raw_ucb", "random_rec"):
            if algorithm == "central_fewa" and fatigue == 0:
                continue
            full = simulate_algorithm(algorithm, case, instance, fatigue, times,
                                      np.uint64(123), np.uint64(456), c)
            sparse = simulate_algorithm(algorithm, case, instance, fatigue, times,
                                        np.uint64(123), np.uint64(456), c, metrics, prepared)
            for key in metrics:
                assert np.array_equal(full[key], sparse[key], equal_nan=True), (algorithm, fatigue, key)
            direct = simulate_communication(algorithm, case, times, np.uint64(456), c, prepared)
            for key in COMMUNICATION_METRICS:
                assert np.array_equal(full[key], direct[key], equal_nan=True), (algorithm, fatigue, key)
    return "Self-check passed: oracle, windows, synchronous updates, parallel reproducibility, selective logging, and direct communication counts."


def _write_endpoint_csv(folder, unit, data, c):
    """Write two long-format tables per complete learning scenario, pairing by scenario, decay mechanism, and replicate."""
    case = unit["case"]
    n = case["n"]
    oracle = unit["oracle"]
    reference = "bgosine"
    common_info = {
        "case_id": case["case_id"], "group": case["group"], "scenario": case["label"],
        "instance_kind": case["instance_kind"], "instance_index": case["instance_index"],
        "network": case["network"], "family": case["family"], "gap": case["gap"],
        "exp_rate": case["exp_rate"], "fatigue": unit["fatigue"],
        "n": n, "K": case["K"], "T": case["T"], "base_seed": c["SEED"],
        "planned_repeats": case["repeat_count"],
        "oracle_status": ("not_computed" if oracle is None else
                          "exact" if oracle["exact"] else "bounds"),
    }
    # draw_ready sorts shared replicates. Look up the reference by replicate ID to keep seeds paired.
    reference_values = {r["repeat"]: float(r["team_value"][-1])
                        for r in data.get(reference, [])}
    endpoint_rows, paired_rows = [], []
    for name, results in data.items():
        differences = []
        for r in results:
            repeat = int(r["repeat"])
            team_value = float(r["team_value"][-1])
            reward_seed, comm_seed = _paired_seeds(c, case, repeat)
            regret = lower = upper = difference = None
            if oracle is not None:
                lower = (float(oracle["lo"][-1]) - team_value) / n
                upper = (float(oracle["hi"][-1]) - team_value) / n
                if oracle["exact"]:
                    regret = lower
                else:
                    lower = max(0.0, lower)
            if repeat in reference_values:
                difference = (reference_values[repeat] - team_value) / n
                differences.append(difference)
            endpoint_rows.append(dict(
                common_info, algorithm=name, repeat=repeat,
                reward_seed_hex=f"0x{int(reward_seed):016x}",
                comm_seed_hex=f"0x{int(comm_seed):016x}",
                expected_reward_per_agent=team_value / n,
                regret_per_agent=regret, regret_lower=lower, regret_upper=upper,
                regret_minus_bgosine=difference,
                first_90pct_hold_time=r.get("first_90pct_hold_time"),
            ))
        if name != reference and differences:
            mean, half, count = _report_stats(differences)
            paired_rows.append(dict(
                common_info, reference=reference, competitor=name, paired_repeats=int(count),
                mean_regret_competitor_minus_reference=float(mean),
                ci95_lower=float(mean - half) if count > 1 else None,
                ci95_upper=float(mean + half) if count > 1 else None,
            ))
    for filename, rows in (("endpoints.csv", endpoint_rows), ("paired_regret.csv", paired_rows)):
        if rows:
            path = folder / filename
            new_file = not path.exists()
            with path.open("a", encoding="utf-8-sig", newline="") as stream:
                writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
                if new_file:
                    writer.writeheader()
                writer.writerows(rows)


def run_suite(config=None):
    c = copy.deepcopy(CONFIG if config is None else config)
    validate_config(c)
    cases, plan = build_plot_plan(c)
    plots = _plot_settings(c)
    _report_font(plots)
    started = time.perf_counter()
    if c["SELF_CHECK"]:
        print(self_check(c), flush=True)
    _prewarm(c)
    trajectory_count = sum(unit["case"]["repeat_count"] * len(unit["algorithms"])
                           for unit in plan if not unit["communication_only"])
    expected_pictures = sum(len(unit["stems"]) for unit in plan)
    print(f"Planned parameter settings: {len(cases)}. Selected experiment combinations: {len(plan)}. Expected figures: {expected_pictures}.", flush=True)
    print(f"Full algorithm trajectories: {trajectory_count}. Communication-only plots replay the communication random stream directly.", flush=True)
    # Share read-only inputs within each parameter setting and keep random samples separate across cases.
    prepared_cases = {}
    for unit in plan:
        case = unit["case"]
        if case["case_id"] not in prepared_cases:
            prepared_cases[case["case_id"]] = prepare_simulation(case, c)
        unit["prepared"] = prepared_cases[case["case_id"]]
        unit["times"] = make_checkpoints(case["T"], c)
        unit["instance"] = None if unit["communication_only"] else make_instance(case, c)
        unit["oracle"] = _plot_oracle(unit, c)
        unit["results"] = {name: {} for name in unit["algorithms"]}
        unit["drawn"] = False
    workers = _choose_workers(c, plan)
    base = Path(c["OUTPUT"]["DIRECTORY"]) if c["OUTPUT"]["DIRECTORY"] else Path(__file__).resolve().parent / "anv_results"
    folder = base / ("figures_" + datetime.now().strftime("%Y%m%d_%H%M%S_%f"))
    folder.mkdir(parents=True, exist_ok=False)
    print(f"Worker threads: {workers}. Output directory: {folder}", flush=True)
    hours = c["EXECUTION"]["MAX_HOURS"]
    deadline = math.inf if hours is None else time.perf_counter() + 3600 * hours
    # Queue the largest jobs first to avoid a slow final trajectory. Job order does not affect the seeds.
    algorithm_weight = {"eff_raw_ucb": 16, "eff_fewa": 10, "fewa": 20, "full_ucb": 3,
                        "coop_eff_fewa": 2, "random_rec": 0.3,
                        "central_fewa": 1, "bgosine": 0.3, "no_comm": 0.2}
    jobs = [(index, name, repeat) for index, unit in enumerate(plan)
            for name in unit["algorithms"] for repeat in range(unit["case"]["repeat_count"])]
    jobs.sort(key=lambda job: 0 if plan[job[0]]["communication_only"] else (
        plan[job[0]]["case"]["T"] * plan[job[0]]["case"]["n"] * plan[job[0]]["case"]["K"]
        * algorithm_weight.get(job[1], 1)), reverse=True)
    completed = 0
    stopped = False
    failed = False
    pool = ThreadPoolExecutor(max_workers=workers)
    futures = {}
    def draw_ready(partial=False):
        for unit in plan:
            if unit["drawn"]:
                continue
            common = sorted(set.intersection(*(set(values) for values in unit["results"].values())))
            if not common or (not partial and len(common) != unit["case"]["repeat_count"]):
                continue
            case, fatigue = unit["case"], unit["fatigue"]
            data = {name: [unit["results"][name][repeat] for repeat in common]
                    for name in unit["algorithms"]}
            meta = dict(case, fatigue=fatigue,
                        title=case["label"] + f", {'individual' if fatigue == 0 else 'shared'} decay, n={case['n']}, K={case['K']}")
            settings = dict(plots, selected_stems=unit["stems"],
                            filename_prefix=_case_picture_prefix(unit["case_number"], case, fatigue))
            if c["OUTPUT"].get("SAVE_ENDPOINT_CSV", False) and not unit["communication_only"]:
                _write_endpoint_csv(folder, unit, data, c)
            report_case(folder, meta, data, unit["oracle"], settings)
            unit["results"].clear()
            unit["drawn"] = True
            print(f"Plotted: {meta['title']} ({len(common)}/{case['repeat_count']} replicates)", flush=True)
    try:
        # Submit lightweight job descriptions. Workers allocate simulation arrays and continue computing during plotting.
        for index, name, repeat in jobs:
            future = pool.submit(_calculate_plot_sample, plan[index], name, repeat, c)
            futures[future] = (index, name, repeat)
        while futures:
            if time.perf_counter() >= deadline and not stopped:
                stopped = True
                for future in futures:
                    future.cancel()
                print("Time limit reached. Canceling pending tasks and waiting for running tasks before plotting completed pairs.", flush=True)
            ready, _ = wait(futures, timeout=1.0, return_when=FIRST_COMPLETED)
            for future in ready:
                index, name, repeat = futures.pop(future)
                if future.cancelled():
                    continue
                plan[index]["results"][name][repeat] = future.result()
                completed += 1
                if completed == 1 or completed % c["EXECUTION"]["PROGRESS_EVERY"] == 0 or not futures:
                    print(f"Completed {completed}/{len(jobs)} tasks in {(time.perf_counter()-started)/60:.1f} min.", flush=True)
            draw_ready()
    except KeyboardInterrupt:
        stopped = True
        print("Interrupted. Canceling pending tasks and waiting for running tasks before plotting completed pairs.", flush=True)
        for future in futures:
            future.cancel()
    except Exception:
        failed = True
        for future in futures:
            future.cancel()
        raise
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
        if stopped and not failed:
            for future, (index, name, repeat) in futures.items():
                if not future.cancelled():
                    plan[index]["results"][name][repeat] = future.result()
            draw_ready(partial=True)
    images = sorted(folder.glob("*.png"))
    if not stopped and c["OUTPUT"]["SAVE_PLOTS"] and len(images) != expected_pictures:
        raise AssertionError(f"Expected {expected_pictures} PNG files, found {len(images)}. Check the configuration and metrics.")
    elapsed = time.perf_counter() - started
    status = "Interrupted or timed out. Restarting will repeat the calculations" if stopped else "Completed"
    print(f"{status}. PNG files: {len(images)}. Elapsed time: {elapsed/60:.2f} min.\n{folder}", flush=True)
    return dict(status=status, summary_directory=str(folder), images=[str(path) for path in images],
                workers=workers, elapsed_seconds=elapsed, completed_tasks=completed,
                planned_trajectories=trajectory_count, expected_pictures=expected_pictures)


def main(config=None):
    return run_suite(CONFIG if config is None else config)


if __name__ == "__main__" and CONFIG["RUN"]:
    RESULTS = main()
