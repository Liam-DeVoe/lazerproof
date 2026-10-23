"""Random APIMod lists (JSON) for the beatmap differential test.

gen_mods(rng, allowed) -> JSON string: 0..5 mods in random order (duplicates and incompatible
combinations allowed: lazer applies whatever list it is given), each with randomised settings that
exercise APIMod.ToMod (in-range / off-grid / out-of-range numbers, ints for doubles, strings, bools,
nulls, huge integers, unknown keys).
"""
import json, random, struct

# acronym -> list of (key, kind, lo, hi)
SETTINGS = {
    'EZ': [('retries', 'int', 0, 10)],
    'NF': [], 'HR': [], 'TC': [], 'BL': [], 'ST': [], 'AL': [], 'SG': [], 'AT': [], 'CN': [], 'RX': [], 'AP': [],
    'SO': [], 'TR': [], 'SI': [], 'FR': [], 'BU': [], 'SY': [], 'TD': [], 'SV2': [],
    'HT': [('speed_change', 'double', 0.5, 0.99), ('adjust_pitch', 'bool')],
    'DC': [('speed_change', 'double', 0.5, 0.99)],
    'DT': [('speed_change', 'double', 1.01, 2), ('adjust_pitch', 'bool')],
    'NC': [('speed_change', 'double', 1.01, 2)],
    'SD': [('fail_on_slider_tail', 'bool'), ('restart', 'bool')],
    'PF': [('restart', 'bool')],
    'HD': [('only_fade_approach_circles', 'bool')],
    'FL': [('follow_delay', 'double', 120, 1200), ('size_multiplier', 'float', 0.5, 2), ('combo_based_size', 'bool')],
    'AC': [('minimum_accuracy', 'double', 0.6, 0.999), ('accuracy_judge_mode', 'enum', 0, 1), ('restart', 'bool')],
    'TP': [('seed', 'seed'), ('metronome', 'bool')],
    'DA': [('circle_size', 'diff', 0, 11), ('approach_rate', 'diff', -10, 11), ('drain_rate', 'diff', 0, 11),
           ('overall_difficulty', 'diff', 0, 11), ('extended_limits', 'bool')],
    'CL': [('no_slider_head_accuracy', 'bool'), ('classic_note_lock', 'bool'), ('always_play_tail_sample', 'bool'),
           ('fade_hit_circle_early', 'bool'), ('classic_health', 'bool')],
    'RD': [('angle_sharpness', 'float', 1, 10), ('seed', 'seed')],
    'MR': [('reflection', 'enum', 0, 2)],
    'WG': [('strength', 'double', 0.1, 2)],
    'GR': [('start_scale', 'float', 0, 0.99)],
    'DF': [('start_scale', 'float', 1, 25)],
    'WU': [('initial_rate', 'double', 0.5, 1.99), ('final_rate', 'double', 0.51, 2), ('adjust_pitch', 'bool')],
    'WD': [('initial_rate', 'double', 0.51, 2), ('final_rate', 'double', 0.5, 1.99), ('adjust_pitch', 'bool')],
    'BR': [('spin_speed', 'double', 0.02, 12), ('direction', 'enum', 0, 1)],
    'AD': [('scale', 'float', 1.5, 10), ('style', 'enum', 0, 9)],
    'MU': [('inverse_muting', 'bool'), ('enable_metronome', 'bool'), ('mute_combo_count', 'int', 0, 500),
           ('affects_hit_sounds', 'bool')],
    'NS': [('hidden_combo_count', 'int', 0, 50)],
    'MG': [('attraction_strength', 'float', 0.05, 1)],
    'RP': [('repulsion_strength', 'float', 0.05, 1)],
    'AS': [('initial_rate', 'double', 0.5, 2), ('adjust_pitch', 'bool')],
    'DP': [('max_depth', 'float', 50, 200), ('show_approach_circles', 'bool')],
    'BM': [('max_size_combo_count', 'int', 5, 100), ('max_cursor_size', 'float', 5, 15)],
}

# mods with beatmap-side effects get extra weight
BEATMAP_MODS = ['EZ', 'HR', 'DA', 'ST', 'MR', 'CL', 'HD', 'TC', 'FR', 'WU', 'WD', 'AS', 'TP', 'RD', 'GR', 'DF', 'SI',
                'TR', 'WG', 'DP']

ENUM_NAMES = {'reflection': ['Horizontal', 'Vertical', 'Both'], 'accuracy_judge_mode': ['MaximumAchievable', 'Standard'],
              'direction': ['Clockwise', 'Counterclockwise'],
              'style': ['Linear', 'Gravity', 'InOut1', 'InOut2', 'Accelerate1', 'Accelerate2', 'Accelerate3',
                        'Decelerate1', 'Decelerate2', 'Decelerate3']}


class Raw:
    """A JSON number written verbatim (to control long vs double classification)."""
    def __init__(self, text): self.text = text


def fnum(rng, x):
    """A double JSON token for x (always contains '.' or 'e')."""
    t = repr(float(x))
    if 'inf' in t or 'nan' in t:
        t = '1e300'
    if '.' not in t and 'e' not in t:
        t += '.0'
    return Raw(t)


def numeric(rng, lo, hi, grid):
    r = rng.random()
    if r < 0.35:   # on grid
        k = rng.randint(round(lo / grid), round(hi / grid))
        return fnum(rng, k * grid) if rng.random() < 0.8 else Raw(f'{k * grid:.{max(0, len(str(grid)) - 2)}f}')
    if r < 0.6:    # off grid in range
        return fnum(rng, rng.uniform(lo, hi))
    if r < 0.7:    # half-grid ties (decimal round-half-even)
        k = rng.randint(round(lo / grid), round(hi / grid))
        s = f'{(k + 0.5) * grid:.6f}'.rstrip('0')
        return Raw(s if '.' in s else s + '.0')
    if r < 0.8:    # out of range
        return fnum(rng, rng.choice([lo - rng.uniform(0, 5), hi + rng.uniform(0, 5), -1e30, 1e30, 0.0, -0.0]))
    if r < 0.88:   # integer token
        return Raw(str(rng.randint(int(lo) - 2, int(hi) + 2)))
    if r < 0.94:   # string
        return rng.choice([f'{rng.uniform(lo, hi):.3f}', ' 1.5 ', 'abc', '', '1,5', 'NaN', 'Infinity', '-0', str(rng.randint(0, 3))])
    return rng.choice([True, False, None, Raw('123456789012345678901234567890')])


def value(rng, kind, lo=None, hi=None, key=''):
    if kind == 'bool':
        return rng.choice([True, False, True, False, 1, 0, '1', '0', 'true', 'False', ' TRUE ', 'yes', None, Raw('2.5'), Raw('0.0')])
    if kind == 'int':
        r = rng.random()
        if r < 0.6: return Raw(str(rng.randint(lo, hi)))
        if r < 0.75: return Raw(str(rng.choice([lo - rng.randint(1, 100), hi + rng.randint(1, 100), 2**31, -2**31 - 1, 2**40])))
        if r < 0.9: return fnum(rng, rng.choice([rng.uniform(lo, hi), rng.randint(lo, hi) + 0.5, 2.5, 3.5, -0.5]))
        return rng.choice([str(rng.randint(lo, hi)), ' 7 ', '+3', '1e2', 'x', True, None])
    if kind == 'double':
        grid = {('follow_delay'): 120}.get(key, 0.001 if key == 'minimum_accuracy' else (0.1 if key == 'strength' else 0.01))
        return numeric(rng, lo, hi, grid)
    if kind == 'float':
        grid = {'size_multiplier': 0.1, 'angle_sharpness': 0.1, 'start_scale': 0.01 if hi < 1 else 0.1, 'scale': 0.1,
                'attraction_strength': 0.05, 'repulsion_strength': 0.05, 'max_depth': 10, 'max_cursor_size': 0.5}.get(key, 0.1)
        return numeric(rng, lo, hi, grid)
    if kind == 'diff':
        r = rng.random()
        if r < 0.1: return None
        if r < 0.7: return fnum(rng, round(rng.uniform(lo - 1, hi + 1), rng.choice([1, 1, 2, 6])))
        if r < 0.8: return Raw(str(rng.randint(lo - 3, hi + 3)))
        if r < 0.9: return rng.choice(['5.5', '', ' 7 ', 'abc', 'NaN', '-Infinity', '1e3'])
        return fnum(rng, rng.choice([-1e30, 1e30, -0.0, 10.000001, 11.5, -10.5]))
    if kind == 'enum':
        r = rng.random()
        if r < 0.5: return Raw(str(rng.randint(lo, hi)))
        if r < 0.75: return rng.choice(ENUM_NAMES[key])
        return rng.choice([Raw(str(hi + 1)), Raw('-1'), fnum(rng, 1.0), Raw('1.5'), ' ' + ENUM_NAMES[key][0], 'both',
                           ENUM_NAMES[key][0] + ', ' + ENUM_NAMES[key][-1], '1', True, None, Raw('99999999999')])
    if kind == 'seed':
        r = rng.random()
        if r < 0.8: return Raw(str(rng.randint(-2**31, 2**31 - 1)))
        return rng.choice([Raw(str(rng.randint(0, 1000))), str(rng.randint(0, 100000)), fnum(rng, rng.randint(0, 99999) + 0.5),
                           Raw(str(-2**31)), Raw(str(2**31 - 1))])
    raise ValueError(kind)


def dumps(v):
    if isinstance(v, Raw): return v.text
    if isinstance(v, dict): return '{' + ','.join(json.dumps(k) + ':' + dumps(x) for k, x in v.items()) + '}'
    if isinstance(v, list): return '[' + ','.join(dumps(x) for x in v) + ']'
    return json.dumps(v)


def gen_mod(rng, acr):
    defs = SETTINGS.get(acr, [])
    s = {}
    for d in defs:
        p = 1.0 if d[1] == 'seed' else 0.6
        if rng.random() < p:
            s[d[0]] = value(rng, d[1], *(d[2:] if len(d) > 2 else (None, None)), key=d[0])
    if rng.random() < 0.05:
        s['unknown_key'] = 1
    m = {'acronym': acr}
    if s or rng.random() < 0.3:
        m['settings'] = s
    if acr in ('TP', 'RD') and 'seed' not in s:
        m.setdefault('settings', {})['seed'] = Raw(str(rng.randint(0, 2**31 - 1)))
    return m


def gen_mods(rng, allowed=None, single=None):
    pool = allowed or list(SETTINGS)
    if single:
        mods = [gen_mod(rng, single)]
    else:
        n = rng.choice([1, 1, 2, 2, 3, 3, 4, 5])
        weights = [4 if a in BEATMAP_MODS else 1 for a in pool]
        mods = [gen_mod(rng, rng.choices(pool, weights)[0]) for _ in range(n)]
        if rng.random() < 0.03:
            mods.append({'acronym': rng.choice(['XX', 'dt', 'ZZ'])})
    return dumps(mods)


if __name__ == '__main__':
    import sys
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    for _ in range(10):
        print(gen_mods(rng))
