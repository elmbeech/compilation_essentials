###
# title: linscan_timing.py
# language: python3
#
# date: 2024-12-07
# license: GPLv3
# author: bue, willem
#
# run: pyton3 linscan_timing.py
#
# reference:
#   Massimiliano Poletto and Vivek Sarkar 1999 Linear scan register allocation
#   https://doi.org/10.1145/330249.330250
#
# descriprion:
#   code to execute and time test runs.
#####



# library
import matplotlib.pyplot as plt
import os
import pandas as pd
import sys
import time


# const
s_path = 'tests/linscan/'
ls_file = [
    # parallel
    'parallel_k0004.py',
    'parallel_k0008.py',
    'parallel_k0012.py',
    'parallel_k0016.py',
    'parallel_k0020.py',
    'parallel_k0024.py',
    'parallel_k0028.py',
    'parallel_k0032.py',
    'parallel_k0036.py',
    'parallel_k0040.py',
    'parallel_k0044.py',
    'parallel_k0048.py',
    'parallel_k0052.py',
    'parallel_k0056.py',
    'parallel_k0060.py',
    'parallel_k0064.py',
    'parallel_k0068.py',
    'parallel_k0072.py',
    'parallel_k0076.py',
    'parallel_k0080.py',
    'parallel_k0084.py',
    'parallel_k0088.py',
    'parallel_k0092.py',
    'parallel_k0096.py',
    'parallel_k0100.py',
    'parallel_k0104.py',
    'parallel_k0108.py',
    'parallel_k0112.py',
    'parallel_k0116.py',
    'parallel_k0120.py',
    'parallel_k0124.py',
    'parallel_k0128.py',
    # serial
    'serial_m4_k0004.py',
    'serial_m4_k0008.py',
    'serial_m4_k0012.py',
    'serial_m4_k0016.py',
    'serial_m4_k0020.py',
    'serial_m4_k0024.py',
    'serial_m4_k0028.py',
    'serial_m4_k0032.py',
    'serial_m4_k0036.py',
    'serial_m4_k0040.py',
    'serial_m4_k0044.py',
    'serial_m4_k0048.py',
    'serial_m4_k0052.py',
    'serial_m4_k0056.py',
    'serial_m4_k0060.py',
    'serial_m4_k0064.py',
    'serial_m4_k0068.py',
    'serial_m4_k0072.py',
    'serial_m4_k0076.py',
    'serial_m4_k0080.py',
    'serial_m4_k0084.py',
    'serial_m4_k0088.py',
    'serial_m4_k0092.py',
    'serial_m4_k0096.py',
    'serial_m4_k0100.py',
    'serial_m4_k0104.py',
    'serial_m4_k0108.py',
    'serial_m4_k0112.py',
    'serial_m4_k0116.py',
    'serial_m4_k0120.py',
    'serial_m4_k0124.py',
    'serial_m4_k0128.py',
]

i_run = 5


# generate oupt file
f = open('linscan_timing.csv', 'w')
f.close()
f = open('linscan_spills.csv', 'w')
f.close()

# generate data
lls_data = []
for s_file in ls_file:
    for s_alloc, s_runtest in [
            ('graph_coloring','run-tests-tup.py'),
            ('linear_scan', 'run-tests-linscan.py')
        ]:
        for i in range(i_run):
            # run
            #s_command = f'python3 {s_runtest} {s_path}{s_file}'
            s_command = f'python3 {s_runtest} {s_path}{s_file} > /dev/null 2>&1'
            print(f'processing: {s_alloc} {s_file} {i+1}/{i_run} {s_command}...')
            #r_start = time.time()
            os.system(s_command)
            #time.sleep(1)
            #r_stop = time.time()
            #r_runtime = (r_stop - r_start) / 100
            s_integration = s_file.split('_')[0]
            i_variable = int(s_file.split('_')[-1].replace('k','').replace('.py',''))
            ls_data = [s_alloc, s_integration, i_variable, i]
            lls_data.append(ls_data)

df_tag = pd.DataFrame(lls_data, columns = ['allocation', 'variable_integration','variable_n','run'])
df_time = pd.read_csv('linscan_timing.csv', header=None)
df_time.columns = ['runtime_ms']
df_spill = pd.read_csv('linscan_spills.csv', header=None)
df_spill.columns = ['spill_n']

if (df_tag.shape[0] != df_time.shape[0]) or (df_tag.shape[0] != df_spill.shape[0]):
    sys.exit(f'Error: shape df_tag {df_tag.shape}, df_time {df_time.shape}, df_spill {df_spill.shape} datafarme row number does not match.')

df_data = pd.merge(df_tag, df_time, left_index=True, right_index=True)
df_data = pd.merge(df_data, df_spill, left_index=True, right_index=True)
#print(df_data)

# generate plot
df_ave = df_data.groupby(['allocation','variable_integration','variable_n']).median().reset_index()
df_ave.drop('run', axis=1, inplace=True)
df_ave['run'] = df_ave.allocation + '_' + df_ave.variable_integration
print(df_ave)

# complation time
fig, ax = plt.subplots(figsize=(11, 8.5))
for s_run in sorted(df_ave['run'].unique()):
    df_ave.loc[df_ave.run == s_run, :].plot(
        x = 'variable_n',
        y = 'runtime_ms',
        style = 's:',
        ylabel = 'runtime_ms',
        label = s_run,
        grid = True,
        title = 'Register allocation compilation time',
        ax = ax
    )
plt.tight_layout()
fig.savefig('linscan_timing.png', facecolor='white')

# spills
fig, ax = plt.subplots(figsize=(11, 8.5))
for s_run in sorted(df_ave['run'].unique()):
    df_ave.loc[df_ave.run == s_run, :].plot(
        x = 'variable_n',
        y = 'spill_n',
        style = 'o:',
        ylabel = 'spill_n',
        label = s_run,
        grid = True,
        title = 'Register allocation spills',
        ax = ax
    )
plt.tight_layout()
fig.savefig('linscan_spills.png', facecolor='white')

