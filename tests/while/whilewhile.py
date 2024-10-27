summ = 0
m = input_int()
n = input_int()
i = 1
while i < m:
    j = 1
    while j < n:
        summ = ((summ + i) + j)
        j = (j + 1)
    i = (i + 1)
print(summ)

