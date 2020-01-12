import argparse
import matplotlib.pyplot as plt
from read_results import read_results
from pathlib import Path
import copy
import numpy as np

parser = argparse.ArgumentParser(description='Generate plots for open source experimental results')
parser.add_argument('--single', '-s', action='store_true', help='Generate a single plot with all results. Otherwise generates one per benchmark set')
args = parser.parse_args()

benchmark_sets = ['circular_pointer', 'shift_register', 'arbitrated_n2', 'arbitrated_n3', 'arbitrated_n4', 'arbitrated_n5']
TIMEOUT = 4*3600 # 4 hours in seconds

log_dir = Path('opensource-results')
results = read_results(log_dir)

for b in benchmark_sets:
    sc_time = results[b][['porsc', 'check-en']].sum(axis=1, skipna=False)
    results[b]['sc-time'] = sc_time
    total_time = results[b][['sc-time', 'run-por']].sum(axis=1, skipna=False)
    results[b]['total-por'] = total_time
    idx = results[b]['total-por'].index[results[b]['total-por'] > TIMEOUT]
    results[b]['total-por']

for b in benchmark_sets:
    # replace NaN with the TIMEOUT
    results[b] = results[b].fillna(value=TIMEOUT)

B=TIMEOUT

if args.single:
    ax = plt.gca()
    fig = plt.gcf()
    ax.set_xscale('log')
    ax.set_yscale('log')
    plt.plot([0, B], [0, B])
    plt.plot([0, B], [B, B], 'k')
    plt.plot([B, B], [0, B], 'k')
    plt.plot([0, B], [0, B/10], 'k--', linewidth=1.0)
    plt.plot([0, B/10], [0, B], 'k--', linewidth=1.0)
    plt.plot([0, B], [0, B/100], 'k--', linewidth=1.0)
    plt.plot([0, B/100], [0, B], 'k--', linewidth=1.0)
    ax.set_aspect('equal', adjustable='box')
    ax.spines['right'].set_visible(False)
    ax.spines['top'].set_visible(False)

    for b in benchmark_sets:
        plt.scatter(results[b]['run'], results[b]['total-por'], facecolors='none', edgecolor='b')

    ax.set_ylabel('BMC with POR and RIS', fontsize=20)
    ax.set_xlabel('Regular BMC', fontsize=20)
    fig.tight_layout()
    plt.show()
else:
    fig, axs = plt.subplots(3, 2, figsize=(10, 8))
    axs = axs.flatten()

    for ax, b in zip(axs, benchmark_sets):
        ax.set_xscale('log')
        ax.set_yscale('log')
        ax.plot([0, B], [0, B])
        ax.plot([0, B], [B, B], 'k')
        ax.plot([B, B], [0, B], 'k')
        ax.plot([0, B], [0, B/10], 'k--', linewidth=1.0)
        ax.plot([0, B/10], [0, B], 'k--', linewidth=1.0)
        ax.plot([0, B], [0, B/100], 'k--', linewidth=1.0)
        ax.plot([0, B/100], [0, B], 'k--', linewidth=1.0)
        #ax.scatter([B - B/10], [0], 'r')
        #ax.plot([0, 0], [B, 0], 'k')
        #ax.plot([B, 0], [B, B], 'k')
        #ax.plot([0, B], [B, B], 'k')
        ax.scatter(results[b]['run'], results[b]['total-por'], s=100, facecolors='none', edgecolor='b')
        ax.set_ylabel('BMC with POR and RIS', fontsize=20)
        ax.set_xlabel('Regular BMC', fontsize=20)
        #ax.set_title(b, fontweight='bold', size=20)
        ax.set_title(b, fontweight='bold', size=20)
        ax.set_aspect('equal', adjustable='box')
        ax.spines['right'].set_visible(False)
        ax.spines['top'].set_visible(False)
        #ax.axis('off')
    # plt.axis([0, B, 0, B])
    fig.tight_layout()
    plt.show()
