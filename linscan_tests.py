###
# title: linscan_tests.py
# language: python3
#
# date: 2024-12-05
# license: GPLv3
# author: bue, willem
#
# run: pyton3 linscan_tests.py
#
# reference:
#   Massimiliano Poletto and Vivek Sarkar 1999 Linear scan register allocation
#   https://doi.org/10.1145/330249.330250
#
# descriprion:
#   generates the test code for linear scan register allocation.
#   test scriptys were inspired by the 1999 publication Fig 4 and Fig 5.
#####



# library
import os
from pathlib import Path
import string

# processing
s_path = 'tests/linscan/'
os.makedirs(s_path, exist_ok=True)
for k in [2**0, 2**1, 2**2, 2**3, 2**4, 2**5, 2**6, 2**7, 2**8, 2**9, 2**10]:

    # serial variables
    for m in [4]: #[4, 8, 16, 32]
        ls_var_serial = [string.ascii_letters[i] for i in range(m)]
        ls_out_serial = []
        total = 0
        result = None
        for i in range(k):
            s_var_serial = ls_var_serial[i % m]
            ls_out_serial.append(f'{s_var_serial} = {i}\n')
            total += i
            if s_var_serial == ls_var_serial[-1]:
                ls_out_serial.append(f"total = {' + '.join(ls_var_serial)}\n")
                result = total
                total = 0
        ls_out_serial.append('print(total)\n')
        # output file
        s_filename = f'{s_path}/serial_m{m}_k{str(k).zfill(4)}'
        Path(f'{s_filename}.in').touch()
        f = open(f'{s_filename}.py', 'w')
        f.writelines(ls_out_serial)
        f.close()
        f = open(f'{s_filename}.golden', 'w')
        f.write(str(result))
        f.close()

    # parallel variables
    ls_var_parallel = [f'var{str(i).zfill(4)}' for i in range(k)]
    ls_out_parallel = [f'{s} = 1\n' for s in ls_var_parallel]
    ls_out_parallel.append(f"total = {' + '.join(ls_var_parallel)}\n")
    ls_out_parallel.append('print(total)\n')
    # output file
    s_filename =f'{s_path}/parallel_k{str(k).zfill(4)}'
    Path(f'{s_filename}.in').touch()
    f = open(f'{s_filename}.py', 'w')
    f.writelines(ls_out_parallel)
    f.close()
    f = open(f'{s_filename}.golden', 'w')
    f.write(str(len(ls_var_parallel)))
    f.close()

