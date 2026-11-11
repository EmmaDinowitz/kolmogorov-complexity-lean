import sys, re
def fill(path, name, proof):
    s = open(path, encoding='utf-8').read()
    i = s.find(f'theorem {name} ')
    if i < 0: i = s.find(f'theorem {name}\n')
    assert i >= 0, name
    j = s.find(':= by\n  sorry', i)
    assert j >= 0, name
    k = s.find('\n', j)  # end of ':= by' line
    # replace '  sorry' line
    k2 = s.find('\n', k + 1)
    assert s[k+1:k2] == '  sorry', (name, s[k+1:k2])
    body = '\n'.join('  ' + l if l else l for l in proof.strip('\n').split('\n'))
    s = s[:k+1] + body + s[k2:]
    open(path, 'w', encoding='utf-8').write(s)
