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
    #'parallel_k0001.py',  # code causes error!
    #'parallel_k0002.py',  # code causes error!
    'parallel_k0004.py',
    'parallel_k0008.py',
    'parallel_k0016.py',
    'parallel_k0032.py',
    'parallel_k0064.py',
    #'serial_m4_k0001.py', # code causes error!
    #'serial_m4_k0002.py', # code causes error!
    'serial_m4_k0004.py',
    'serial_m4_k0008.py',
    'serial_m4_k0016.py',
    'serial_m4_k0032.py',
    'serial_m4_k0064.py',
]

i_run = 4


# generate oupt file
f = open('linscan_timing.csv', 'w')
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
            #s_command = f'python3 {s_runtest} {s_path}{s_file} > /dev/null 2>&1'
            s_command = f'python3 {s_runtest} {s_path}{s_file}'
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
df_data = pd.read_csv('linscan_timing.csv', header=None)
df_data.columns = ['runtime_ms']
if (df_tag.shape[0] != df_data.shape[0]):
    sys.exit(f'Error: shape df_tag {df_tag.shape} and df_data {df_data.shape} datafarme row number does not match.')

df_data = pd.merge(df_tag, df_data, left_index=True, right_index=True)


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
        style = 's:',
        ylabel = 'runtime_ms',
        label = s_run,
        grid = True,
        title = 'register allocation compilation time',
        ax = ax
    )
plt.tight_layout()
fig.savefig('linscan_timing.png', facecolor='white')
