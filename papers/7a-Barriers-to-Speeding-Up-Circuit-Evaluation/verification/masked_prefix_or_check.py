import random
# masked prefix OR
for m in range(1,12):
    for _ in range(200):
        x=[random.randint(0,1) for _ in range(m)]
        y=[]
        for e in range(m):
            g=1 if any(y[:e]) else 0
            y.append(x[e]^g)
        for e in range(m):
            assert y[e]==x[e]^(1 if any(x[:e]) else 0)
print("masked prefix OR ok")
