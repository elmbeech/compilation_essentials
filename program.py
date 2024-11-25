def mapp(f : Callable[[int], int], v : tuple[int, int]) -> tuple[int, int]:
    return(f(v[0]), f(v[1]))

def inc(x : int) -> int:
    return x + 1

print(mapp(inc, (0, 41))[1])

