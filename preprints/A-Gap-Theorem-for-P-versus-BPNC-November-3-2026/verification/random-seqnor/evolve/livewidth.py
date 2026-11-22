# Live width of test-bed instances (NOTE.md §5j): W(i) = #{p < i : some gate g >= i reads p}.
# An exact expression of any later position over the cut at i needs at most W(i) variables, so
# bounded-support substitution with support K follows the circuit wherever W <= K.
# usage: python3 -I livewidth.py file.bin ...
import struct, sys
for path in sys.argv[1:]:
    with open(path, 'rb') as fh:
        n = struct.unpack('<i', fh.read(4))[0]; j = [0] + list(struct.unpack('<%di' % n, fh.read(4 * n)))
    last = [0] * (n + 1)                    # last gate reading p
    for g in range(1, n + 1):
        last[g - 1] = max(last[g - 1], g); last[j[g]] = max(last[j[g]], g)
    # W(i) = #{p < i : last[p] >= i}; sweep with a difference array
    diff = [0] * (n + 2)
    for p in range(n + 1):
        if last[p] > p: diff[p + 1] += 1; diff[last[p] + 1] -= 1
    W, cur = [], 0
    for i in range(n + 1):
        cur += diff[i]; W.append(cur)
    Ws = sorted(W)
    print('%-22s n=%-6d max=%-6d median=%-6d 90%%=%d' % (path.split('/')[-1], n, Ws[-1], Ws[len(Ws) // 2], Ws[int(0.9 * len(Ws))]))
