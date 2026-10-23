#!/usr/bin/env python3
"""Random osu! mod lists (lazer APIMod JSON) for the simulation diff test (sim_diff.py --gen-mods POOL).

Random subset of the pool, random order (lazer applies any combination in list order), random settings:
mostly in-range values, sometimes off-grid / out-of-range / omitted / integer-typed, so that the decode
(`APIMod.ToMod`: clamping, decimal precision snapping, WU/WD cross constraints) is exercised too.
"""
import json, random

R2 = lambda rng, lo, hi: round(rng.uniform(lo, hi), 2)


def num(rng, lo, hi, step):
    """A setting value: on-grid in range (mostly), off-grid, out of range, or an integer literal."""
    r = rng.random()
    if r < 0.6:
        k = rng.randint(round(lo / step), round(hi / step))
        return round(k * step, 6)
    if r < 0.8:
        return rng.uniform(lo, hi)
    if r < 0.9:
        return rng.choice([lo - step, hi + step, lo - 1, hi + 1, lo, hi])
    return int(rng.choice([lo, hi, (lo + hi) / 2]))


def b(rng):
    return rng.random() < 0.5


SETTINGS = {
    "EZ": lambda r: {"retries": r.randint(0, 10)} if r.random() < 0.8 else {},
    "NF": lambda r: {},
    "HT": lambda r: {"speed_change": num(r, 0.5, 0.99, 0.01), "adjust_pitch": b(r)},
    "DC": lambda r: {"speed_change": num(r, 0.5, 0.99, 0.01)},
    "DT": lambda r: {"speed_change": num(r, 1.01, 2.0, 0.01), "adjust_pitch": b(r)},
    "NC": lambda r: {"speed_change": num(r, 1.01, 2.0, 0.01)},
    "WU": lambda r: {"initial_rate": num(r, 0.5, 1.99, 0.01), "final_rate": num(r, 0.51, 2.0, 0.01), "adjust_pitch": b(r)},
    "WD": lambda r: {"initial_rate": num(r, 0.51, 2.0, 0.01), "final_rate": num(r, 0.5, 1.99, 0.01), "adjust_pitch": b(r)},
    "AS": lambda r: {"initial_rate": num(r, 0.5, 2.0, 0.01), "adjust_pitch": b(r)},
    "SD": lambda r: {"fail_on_slider_tail": b(r), "restart": b(r)},
    "PF": lambda r: {"restart": b(r)},
    "AC": lambda r: {"minimum_accuracy": num(r, 0.6, 0.999, 0.001), "accuracy_judge_mode": r.choice([0, 1, "Standard", "MaximumAchievable"])},
    "HD": lambda r: {"only_fade_approach_circles": b(r)},
    "FL": lambda r: {"follow_delay": num(r, 120, 1200, 120), "size_multiplier": num(r, 0.5, 2.0, 0.1), "combo_based_size": b(r)},
    "CL": lambda r: {k: b(r) for k in ["no_slider_head_accuracy", "classic_note_lock", "always_play_tail_sample",
                                       "fade_hit_circle_early", "classic_health"] if r.random() < 0.8},
    "HR": lambda r: {},
    "MR": lambda r: {"reflection": r.choice([0, 1, 2])},
    "DA": lambda r: {k: (num(r, -10 if k == "approach_rate" else 0, 11, 0.1) if r.random() < 0.7 else None)
                     for k in ["circle_size", "approach_rate", "drain_rate", "overall_difficulty"] if r.random() < 0.7},
    "SV2": lambda r: {},
    "BL": lambda r: {}, "BU": lambda r: {}, "SY": lambda r: {},
    "MU": lambda r: {"inverse_muting": b(r), "mute_combo_count": r.randint(0, 500)},
    "NS": lambda r: {"hidden_combo_count": r.randint(0, 50)},
    "BM": lambda r: {"max_size_combo_count": r.randint(5, 100)},
    "RX": lambda r: {},
    "AP": lambda r: {},
    "AL": lambda r: {},
    "SG": lambda r: {},
    "SO": lambda r: {},
    "ST": lambda r: {},
    "TD": lambda r: {},
    "GR": lambda r: {"start_scale": num(r, 0.0, 0.99, 0.01)},
    "DF": lambda r: {"start_scale": num(r, 1.0, 25.0, 0.1)},
    "SI": lambda r: {},
    "TR": lambda r: {},
    "WG": lambda r: {"strength": num(r, 0.1, 2.0, 0.1)},
    "TP": lambda r: {"seed": r.randint(-2**31, 2**31 - 1), "metronome": b(r)},
    "RD": lambda r: {"seed": r.randint(-2**31, 2**31 - 1), "angle_sharpness": num(r, 1, 10, 0.1)},
    "DP": lambda r: {"max_depth": num(r, 50, 200, 10), "show_approach_circles": b(r)},
    "MG": lambda r: {"attraction_strength": num(r, 0.05, 1.0, 0.05)},
    "RP": lambda r: {"repulsion_strength": num(r, 0.05, 1.0, 0.05)},
    "BR": lambda r: {"spin_speed": num(r, 0.02, 12, 0.01), "direction": r.choice([0, 1])},
    "FR": lambda r: {},
    "TC": lambda r: {},
    "AD": lambda r: {"scale": num(r, 1.5, 10, 0.1), "style": r.randint(0, 9)},
    "HDo": lambda r: {},
}

POOLS = {
    # M5: rate, fail/health, multiplier, rank, Classic (+ beatmap-side mods to vary the playable)
    "M5": ["EZ", "NF", "HT", "DC", "DT", "NC", "WU", "WD", "AS", "SD", "PF", "AC", "FL", "CL", "HR", "MR", "DA",
           "SV2", "TD"],
    "M5rate": ["HT", "DC", "DT", "NC", "WU", "WD", "AS", "CL", "NF"],
    "M5fail": ["EZ", "NF", "SD", "PF", "AC", "CL", "HR", "DA"],
    "M5hd": ["HD", "FL", "CL", "NF", "HR", "DT"],
    # M6: input mods (+ rate / Classic / fail interplay)
    "M6": ["RX", "AP", "AL", "SG", "SO", "ST", "TD", "CL", "NF", "DT", "HT", "NC", "WU", "AS", "SD", "HR", "EZ"],
    "M6rx": ["RX", "CL", "NF", "HR", "DT"],
    "M6ap": ["AP", "CL", "NF", "DT", "HT", "WD", "AS"],
    "M6alt": ["AL", "SG", "CL", "NF"],
    "M6so": ["SO", "DT", "HT", "WU", "WD", "AS", "NC", "NF"],
    "M6st": ["ST", "NF", "SD", "DT"],
    # M7: drawable transforms / positions (TP keeps its seed: unseeded runs are not reproducible)
    "M7hd": ["HD", "CL", "NF", "HR"],
    "M7gr": ["GR", "DF", "CL", "NF"],
    "M7si": ["SI", "CL", "NF"],
    "M7tp": ["TP", "NF", "CL"],
    "M7wg": ["WG", "CL", "NF"],
    "M7tr": ["TR", "CL", "NF"],
    "M7dp": ["DP", "CL", "NF"],
    "M7mg": ["MG", "CL", "NF"],
    "M7rp": ["RP", "CL", "NF"],
    "M7br": ["BR", "CL", "NF", "HR"],
    # M8: everything (incl. beatmap-side RD/MR/FR/DA and visual-only mods)
    "ALL": ["EZ", "NF", "HT", "DC", "HR", "SD", "PF", "DT", "NC", "HD", "TC", "FL", "BL", "ST", "AC", "TP", "DA", "CL",
            "RD", "MR", "AL", "SG", "RX", "AP", "SO", "TR", "WG", "SI", "GR", "DF", "WU", "WD", "BR", "AD", "MU", "NS",
            "MG", "RP", "AS", "FR", "BU", "SY", "DP", "BM", "TD", "SV2"],
    "M7": ["GR", "DF", "SI", "TR", "WG", "TP", "DP", "MG", "RP", "HD", "FR", "TC", "AD", "CL", "NF", "HR", "DT"],
}


# focused pools always contain their first mod
REQUIRED = {"M6rx", "M6ap", "M6alt", "M6so", "M6st", "M7hd", "M7gr", "M7si", "M7tp", "M7wg", "M7tr", "M7dp", "M7mg", "M7rp", "M7br"}


def gen(rng, pool, kmax=5):
    names = POOLS[pool]
    k = rng.randint(0, min(kmax, len(names)))
    chosen = rng.sample(names, k)
    if pool in REQUIRED and names[0] not in chosen:
        chosen.insert(rng.randint(0, len(chosen)), names[0])
    out = []
    for a in chosen:
        s = SETTINGS[a](rng)
        s = {k: v for k, v in s.items() if k == "seed" or rng.random() < 0.9}
        m = {"acronym": a}
        if s:
            m["settings"] = s
        out.append(m)
    return out


if __name__ == "__main__":
    import sys
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    for _ in range(10):
        print(json.dumps(gen(rng, sys.argv[1] if len(sys.argv) > 1 else "M5")))
