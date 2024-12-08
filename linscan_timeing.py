###
# title: linscan_timeing.py
# language: python3
#
# date: 2024-12-07
# license: GPLv3
# author: bue, willem
#
# run: pyton3 linscan_timeing.py
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
import time


# const
s_path = 'tests/linscan/'
ls_file = [
    'parallel_k0001.py',
    'parallel_k0002.py',
    'parallel_k0004.py',
    'parallel_k0008.py',
    'parallel_k0016.py',
    'parallel_k0032.py',
    'parallel_k0064.py',
    'serial_m4_k0001.py',
    'serial_m4_k0002.py',
    'serial_m4_k0004.py',
    'serial_m4_k0008.py',
    'serial_m4_k0016.py',
    'serial_m4_k0032.py',
    'serial_m4_k0064.py',
]

i_run = 16


# generate data
lls_data = []
for s_file in ls_file:
    for s_alloc, s_runtest in [
            ('graph_coloring','run-tests-tup.py'),
            ('linear_scan', 'run-tests-linscan.py')
        ]:
        for i in range(i_run):
            print(f'processing: {s_alloc} {s_file} {i}/{i_run} ...')

            # run
            s_command = f'python3 {s_runtest} {s_path}{s_file} > /dev/null 2>&1'
            r_start = time.time()
            os.system(s_command)
            r_stop = time.time()
            r_runtime = (r_stop - r_start) / 100
            s_integration = s_file.split('_')[0]
            i_variable = int(s_file.split('_')[-1].replace('k','').replace('.py',''))
            ls_data = [s_alloc, s_integration, i_variable, i, r_runtime]
            lls_data.append(ls_data)

df_data = pd.DataFrame(lls_data, columns=['allocation', 'variable_integration','variable_n','run', 'runtime_ms'])

# generate plot
#print(df_data)
df_ave = df_data.groupby(['allocation','variable_integration','variable_n']).mean().reset_index()
df_ave.drop('run', axis=1, inplace=True)
df_ave['run'] = df_ave.allocation + '_' + df_ave.variable_integration

fig, ax = plt.subplots(figsize=(11, 8.5))
for s_run in sorted(df_ave['run'].unique()):
    df_ave.loc[df_ave.run == s_run, :].plot(
        x = 'variable_n',
        y = 'runtime_ms',
        ylabel = 'runtime_ms',
        label = s_run,
        grid = True,
        title = 'register allocation compilation time',
        ax = ax
    )
plt.tight_layout()
fig.savefig('linscan_timeing.png', facecolor='white')
