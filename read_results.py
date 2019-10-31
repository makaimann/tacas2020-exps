#!/usr/bin/env python3
import argparse
from collections import defaultdict
from pandas import DataFrame
from pathlib import Path
import re
from typing import Any, Dict, Optional, Tuple

time_minsec_pattern = re.compile("(?P<min>\d+)m(?P<sec>\d+\.\d+)")
time_pattern        = re.compile("\d+.\d+")
time_sel, time_id   = 'user', -3

TIMEOUT             = 14400.00

benchmark_pattern   = re.compile("(?P<name>.*)_w(?P<width>\d+)_d(?P<depth>\d+)")

def to_seconds(h, m, s):
    return h*3600.0 + m*60.0 + s

def parse_log(path:Path)->Tuple[Optional[float], bool]:
    time = None
    failed = False

    with path.open() as f:
        contents = f.read().split("\n")
        if not contents:
            failed = True

        if contents[time_id][:len(time_sel)] == time_sel:
            match = re.search(time_pattern, contents[time_id])
            if not match:
                raise RuntimeError("Failed match with: {}, and {}".format(time_pattern, contents[time_id]))
            time = float(match.group())

    return time, failed

def read_results(directory:Path)->Dict[str, DataFrame]:
    failures = list()
    timeouts = list()
    result_dict = defaultdict(list)
    all_params = set()

    for f in directory.rglob("*.log"):
        run = "-".join(f.parts[-2:-1])
        benchmark = f.stem
        match = re.search(benchmark_pattern, benchmark)
        d = match.groupdict()
        name, width, depth = d['name'], int(d['width']), int(d['depth'])
        # Note: ignoring width for now because always the same
        key = (name, run)
        time, failed = parse_log(f)

        if failed:
            failures.append(f)
        elif time is None:
            timeouts.append(f)

        param_key = (depth, width)
        result_dict[key].append((param_key, time))
        all_params.add(param_key)

    # sort the depths for comparison
    all_params = list(sorted(all_params))

    # post-processing
    final_dict = dict()
    for name, run in result_dict:
        params_and_times = sorted(result_dict[(name, run)])
        params = [d for d, t in params_and_times]
        times  = [t for d, t in params_and_times]
        assert params == all_params, "Got {} and expected {}".format(params, all_params)

        if name not in final_dict:
            final_dict[name] = defaultdict(list)
            final_dict['width-depth'] = params
        final_dict[name][run] = times

    for n in final_dict:
        final_dict[n] = DataFrame.from_dict(final_dict[n])

    return final_dict

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Parse results from provided directory")
    parser.add_argument("directory", help="The directory with the results", type=Path)

    args = parser.parse_args()

    df = read_results(args.directory)
    print("Created DataFrame:\n\t", df)
