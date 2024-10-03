x = input_int()
y = input_int()
if ((False or x != y) and (x == y or True)):
    u = x < y
    v = x < y
    w = x > y
    z = x >= y
else:
    u = True
    v = True
    w = True
    z = True
print(((x - y) if not(((u and v) and (w and z))) else 0))
