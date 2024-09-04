# %display latex

import itertools
from itertools import permutations
import json

R = QQ['q']
q = R.0
Sym = SymmetricFunctions(R)
s = Sym.schur()
e = Sym.elementary()
p = Sym.powersum()
h = Sym.homogeneous()

m = Sym.monomial()
f = e.dual_basis()
dp = p.dual_basis()

QSym = QuasiSymmetricFunctions(R)
M = QSym.M()
F = QSym.F()
QS = QSym.QS()

Blasiak_patterns = [
    [[1,2,3], [[2,1,3], [2,3,1]]],
    [[1,3,3], [[2,1,3], [2,3,1]]],
    [[1,3,3], [[3,1,2], [3,2,1]]],
    [[1,2,3], [[3,1,2], [1,3,2]]],
    [[2,2,3], [[3,1,2], [1,3,2]]],
    [[2,2,3], [[3,2,1], [2,3,1]]],
    [[2,3,3], [[3,1,2], [2,3,1]]],
]

Hwang_patterns = [
    [[2,3,3], [[3,1,2], [2,3,1]]],
    [[1,2], [[1,2], [2,1]]],
]

additional_patterns = [
    [[2,3,3,4], [[3,1,4,2], [4,3,1,2]]],
]



def generate_UIO(n, connected=False):
    if connected == False: mode = 1
    else: mode = 2
    seq = [i+mode for i in range(n)]          
    seq[n-1] = n
    list_UIO = [list(seq)]
    while seq[0] < n:
        for i in range(n-1):
            if seq[i] < seq[i+1]:
                seq[i] += 1
                for j in range(i):
                    seq[j] = j+mode
                break
        list_UIO += [list(seq)]
    return list_UIO

def P_inv(P, word):
    inv = 0
    for i in range(1,len(word)):
        for j in range(i):
            if word[i] < word[j] and is_P_less(P, word[i], word[j]) == 0 and is_P_less(P, word[j], word[i]) == 0:
                inv += 1
    return inv

def P_conjugate(P):
    n = len(P)
    lamb = list(Partition([n-h for h in P]).conjugate())
    for i in range(len(lamb),n): lamb.append(0)
    return [n-h for h in lamb]

def is_P_compatible(P, a, b):
    if P[a-1] < b or P[b-1] < a:
        return True
    return False

def is_P_less(P, a, b):
    if P[a-1] < b:
        return True
    return False

def P_Des(P, word):     ## this function returns a composition
    prev = 0
    comp = []
    for i in range(1, len(word)):
        if is_P_less(P, word[i], word[i-1]):
            comp.append(i-prev)
            prev = i
    comp.append(len(word)-prev)
    return comp

def P_Asc(P, word):
    prev = 0
    comp = []
    for i in range(1, len(word)):
        if is_P_less(P, word[i-1], word[i]):
            comp.append(i-prev)
            prev = i
    comp.append(len(word)-prev)
    return comp

def has_rl_P_min(P, word):
    for i in reversed(range(len(word)-1)):
        chk = 0
        for j in range(i+1, len(word)):
            if is_P_less(P, word[i], word[j]) == False:
                chk = 1
                break
        if chk == 0:
            return True
    return False

def has_rl_P_max(P, word):
    for i in reversed(range(len(word)-1)):
        chk = 0
        for j in range(i+1, len(word)):
            if is_P_less(P, word[j], word[i]) == False:
                chk = 1
                break
        if chk == 0:
            return True
    return False

def has_lr_P_min(P, word):
    for i in range(1,len(word)):
        chk = 0
        for j in range(i):
            if is_P_less(P, word[i], word[j]) == False:
                chk = 1
                break
        if chk == 0:
            return True
    return False

def has_lr_P_max(P, word):
    for i in range(1,len(word)):
        chk = 0
        for j in range(i):
            if is_P_less(P, word[j], word[i]) == False:
                chk = 1
                break
        if chk == 0:
            return True
    return False

def is_N_word(P, word, TYPE):
    if len(P) != len(word) or len(word) != sum(TYPE):
        print("Error: Check your input")
        return
    k = 0
    for l in TYPE:
        if has_lr_P_max(P, word[k:k+l]) or P_Des(P, word[k:k+l]) != [l]:
            return False
        k += l
    return True

def N_words(P, TYPE=None):
    N = len(P)
    if TYPE == None:
        TYPE = [N]
    if N != sum(TYPE):
        print("Error: Check your input")
        return
    
    words = []
    for word in Permutations(N):
        word = list(word)
        if is_N_word(P, word, TYPE):
            words.append(word)
    return words

def PTableaux(P, shape=None, reverse=False):
    n = len(P)
    tab_list = []
    if shape == None: shape_list = Partitions(n)
    else: shape_list = [shape]
    for shape in shape_list:
        T = [[0 for j in range(shape[i])] for i in range(len(shape))]
        PTableaux_making(P, shape, T, 0, 0, [i+1 for i in range(n)], tab_list, reverse)
    return tab_list

def PTableaux_making(P, shape, T, r, c, I, tab_list, reverse=False):
    if r == len(shape) and c == 0:
        tab_list.append(Tableau(T))
        return
    elif c == shape[r]:
        PTableaux_making(P, shape, T, r+1, 0, I, tab_list, reverse)
    else:
        for i in I:
            if is_valid_filling(P, T, i, r, c, reverse):
                T[r][c] = i
                PTableaux_making(P, shape, T, r, c+1, [j for j in I if j != i], tab_list, reverse)
                
def is_valid_filling(P, T, a, r, c, reverse=False):
    if reverse == False:
        if r > 0 and is_P_less(P, T[r-1][c], a) == False: return False
        if c > 0 and is_P_less(P, a, T[r][c-1]) == True: return False
    else:
        if r > 0 and is_P_less(P, a, T[r-1][c]) == False: return False
        if c > 0 and is_P_less(P, T[r][c-1], a) == True: return False
    return True

def words_no_des(P):
    words = []
    n = len(P)
    for word in Permutations(n):
        if P_Des(P, word) == [n]:
            words.append(list(word))
    return words

def words_from_heap(P, word):
    words = [list(word)]
    for word in words:
        for i in range(len(word)-1):
            if is_P_compatible(P, word[i], word[i+1]):
                temp = word[:i] + [word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
    return words

def words_from_orbit(P, word):
    words = [list(word)]
    for word in words:
        for i in range(len(word)-1):
            if is_P_compatible(P, word[i], word[i+1]):
                temp = word[:i] + [word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
        for i in range(1,len(word)-1):
            if word[i] < word[i-1] < word[i+1] and is_P_less(P, word[i], word[i+1]) and not is_P_less(P, word[i], word[i-1]) and not is_P_less(P, word[i-1], word[i+1]):
                temp = word[:i-1] + [word[i],word[i+1],word[i-1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if word[i] > word[i+1] > word[i-1] and is_P_less(P, word[i-1], word[i]) and not is_P_less(P, word[i-1], word[i+1]) and not is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i+1],word[i-1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
    return words

def words_from_Blasiak_orbit(P, word):
    words = [list(word)]
    for word in words:
        for i in range(1,len(word)-1):
            if is_P_less(P, word[i], word[i-1]) and (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i], word[i+1]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and (not is_P_less(P, word[i], word[i-1])) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i+1], word[i]) and is_P_less(P, word[i-1], word[i]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i])) and is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i], word[i+1]) and not is_P_compatible(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i+1],word[i-1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i+1], word[i-1]) and not is_P_compatible(P, word[i-1], word[i]) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i],word[i+1],word[i-1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
    return words

def words_from_patterns(P, word, patterns):
    words = [list(word)]
    for word in words:
        for pattern in patterns:
            l = len(pattern[0])
            for i in range(len(word)-l+1):
                chk, corresponding_word = check_pattern(P, word[i:i+l], pattern)
                if chk == True:
                    temp = word[:i]+corresponding_word+word[i+l:]
                    if not temp in words:
                        words.append(temp)
    return words

def words_from_patterns_variant1(P, word, patterns):
    words = [list(word)]
    for word in words:
        for pattern in patterns:
            l = len(pattern[0])
            for i in range(len(word)-l+1):
                chk, corresponding_word = check_pattern(P, word[i:i+l], pattern)
                if chk == True:
                    temp = word[:i]+corresponding_word+word[i+l:]
                    if not temp in words:
                        words.append(temp)
    return words

def words_from_Blasiak_variant1_orbit(P, word):
    words = [list(word)]
    for word in words:
        for i in range(1,len(word)-1):
            if is_P_less(P, word[i], word[i-1]) and (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i], word[i+1]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and (not is_P_less(P, word[i], word[i-1])) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i+1], word[i]) and is_P_less(P, word[i-1], word[i]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i])) and is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i], word[i+1]) and not is_P_compatible(P, word[i+1], word[i-1]) and is_P_compatible(P, word[i-1], word[i]):
                temp = word[:i-1] + [word[i+1],word[i-1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i+1], word[i-1]) and not is_P_compatible(P, word[i-1], word[i]) and is_P_compatible(P, word[i], word[i+1]):
                temp = word[:i-1] + [word[i],word[i+1],word[i-1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
    return words

def words_from_Blasiak_variant2_orbit(P, word):
    words = [list(word)]
    for word in words:
        for i in range(len(word)-1):
            if is_P_compatible(P, word[i], word[i+1]):
                temp = word[:i] + [word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
        for i in range(1,len(word)-1):
            if is_P_less(P, word[i], word[i-1]) and (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i], word[i+1]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and (not is_P_less(P, word[i], word[i-1])) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i+1], word[i]) and is_P_less(P, word[i-1], word[i]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i])) and is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
    return words

def words_from_Blasiak_variant3_orbit(P, word):
    words = [list(word)]
    for word in words:
        for i in range(1,len(word)-1):
            if is_P_less(P, word[i], word[i-1]) and (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i], word[i+1]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and (not is_P_less(P, word[i], word[i-1])) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i+1], word[i]) and is_P_less(P, word[i-1], word[i]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i])) and is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i], word[i+1]) and not is_P_compatible(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i+1],word[i-1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i+1], word[i-1]) and not is_P_compatible(P, word[i-1], word[i]) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i],word[i+1],word[i-1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
        if is_P_compatible(P, word[-1], word[-2]):
            temp = word[:-2] + [word[-1],word[-2]]
            if not temp in words:
                words.append(temp)
    return words

def words_from_Blasiak_variant4_orbit(P, word):
    words = [list(word)]
    for word in words:
        for i in range(1,len(word)-1):
            if is_P_less(P, word[i], word[i-1]) and (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i], word[i+1]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and (not is_P_less(P, word[i], word[i-1])) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i+1], word[i]) and is_P_less(P, word[i-1], word[i]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i])) and is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i], word[i+1]) and not is_P_compatible(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i+1],word[i-1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i+1], word[i-1]) and not is_P_compatible(P, word[i-1], word[i]) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i],word[i+1],word[i-1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
        if is_P_compatible(P, word[0], word[1]):
            temp = [word[1], word[0]] + word[2:]
            if not temp in words:
                words.append(temp)
    return words

def words_from_Blasiak_variant5_orbit(P, word):
    words = [list(word)]
    for word in words:
        for i in range(1,len(word)-1):
            if is_P_less(P, word[i], word[i-1]) and (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i], word[i+1]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and (not is_P_less(P, word[i], word[i-1])) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i-1])) and is_P_less(P, word[i+1], word[i]) and is_P_less(P, word[i-1], word[i]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if (not is_P_less(P, word[i+1], word[i])) and is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i], word[i+1]) and not is_P_compatible(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i+1],word[i-1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i+1], word[i-1]) and not is_P_compatible(P, word[i-1], word[i]) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i],word[i+1],word[i-1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
        if is_P_compatible(P, word[-1], word[-2]):
            temp = word[:-2] + [word[-1],word[-2]]
            if not temp in words:
                words.append(temp)
        if is_P_compatible(P, word[0], word[1]):
            temp = [word[1], word[0]] + word[2:]
            if not temp in words:
                words.append(temp)
    return words

def words_from_Blasiak_variant6_orbit(P, word):
    words = [list(word)]
    for word in words:
        for i in range(1,len(word)-1):
            if is_P_less(P, word[i], word[i-1]) and is_P_less(P, word[i], word[i+1]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i]) and is_P_less(P, word[i-1], word[i]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i], word[i+1]) and not is_P_compatible(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i+1],word[i-1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i+1], word[i-1]) and not is_P_compatible(P, word[i-1], word[i]) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i],word[i+1],word[i-1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
        if is_P_compatible(P, word[-1], word[-2]):
            temp = word[:-2] + [word[-1],word[-2]]
            if not temp in words:
                words.append(temp)
        if is_P_compatible(P, word[0], word[1]):
            temp = [word[1], word[0]] + word[2:]
            if not temp in words:
                words.append(temp)
    return words

def words_from_Blasiak_variant7_orbit(P, word):
    words = [list(word)]
    for word in words:
        for i in range(1,len(word)-1):
            if is_P_less(P, word[i], word[i-1]) and is_P_less(P, word[i], word[i+1]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i-1],word[i+1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i-1]) and is_P_less(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if is_P_less(P, word[i+1], word[i]) and is_P_less(P, word[i-1], word[i]):
                temp = word[:i-1] + [word[i],word[i-1],word[i+1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i], word[i+1]) and not is_P_compatible(P, word[i+1], word[i-1]) and is_P_compatible(P, word[i], word[i-1]):
                temp = word[:i-1] + [word[i+1],word[i-1],word[i]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
            if not is_P_compatible(P, word[i+1], word[i-1]) and not is_P_compatible(P, word[i-1], word[i]) and is_P_compatible(P, word[i+1], word[i]):
                temp = word[:i-1] + [word[i],word[i+1],word[i-1]] + word[i+2:]
                if not temp in words:
                    words.append(temp)
        if is_P_compatible(P, word[-1], word[-2]):
            temp = word[:-2] + [word[-1],word[-2]]
            if not temp in words:
                words.append(temp)
        if is_P_compatible(P, word[0], word[1]):
            temp = [word[1], word[0]] + word[2:]
            if not temp in words:
                words.append(temp)
    return words

def K_orbit(P, word):
    words = words_from_orbit(P, word)
    sym = 0
    for word in words:
        sym += F(P_Des(P, word))
    return h(sym.to_symmetric_function())

def F_gamma(P, words):
    sym = 0
    for word in words:
        sym += F(P_Des(P, word))
    return sym

def q_int(n):
    qint = 0
    for i in range(n):
        qint += q**i
    return qint

def XP(P, mu=None):
    if mu == None:
        words = Permutations(len(P))
    else:
        mu_list = []
        for i in range(len(mu)):
            for j in range(mu[i]):
                mu_list.append(i+1)
        words = Permutations(mu_list)
    sym = 0
    for word in words:
        sym += q**P_inv(P, word) * F(P_Des(P, word))
    return h(sym.to_symmetric_function())

def shape_of_word(P, word, rev=False):
    shape = []
    n = len(word)

    if rev == False:
        k = 1
        while k < n and is_P_less(P, word[k], word[k-1]):
            k += 1
        shape.append(k)
        a = k
        while a < n:
            k += 1
            while k < n and is_P_less(P, word[k], word[k-1]):
                k += 1
            if shape[-1] < k - a: return None
            for i in range(1, k-a+1):
                if is_P_less(P, word[k-i], word[a-i]):
                    return None
            shape.append(k-a)
            a = k
        return Partition(shape).conjugate()
    elif rev == True:
        k = 1
        while k < n and is_P_less(P, word[k-1], word[k]):
            k += 1
        shape.append(k)
        a = k
        while a < n:
            k += 1
            while k < n and is_P_less(P, word[k-1], word[k]):
                k += 1
            if shape[-1] < k - a: return None
            for i in range(1, k-a+1):
                if is_P_less(P, word[a-i], word[k-i]):
                    return None
            shape.append(k-a)
            a = k
        return Partition(shape).conjugate()

def is_1row(shape):
    if shape == None: return False
    if len(shape) == 1: return True
    return False

def is_2row(shape):
    if shape == None: return False
    if len(shape) == 2: return True
    return False

def is_3row(shape):
    if shape == None: return False
    if len(shape) == 3: return True
    return False

def is_hook(shape):
    if shape == None: return False
    if len(shape) == 1 or shape[1] == 1: return True
    return False

def is_2col(shape):
    if shape == None: return False
    if shape[0] == 2: return True
    return False

def is_3col(shape):
    if shape == None: return False
    if shape[0] == 3: return True
    return False

def any_shape(shape):
    if shape == None: return False
    return True

def is_52(shape):
    return shape == [5,2]

def is_43(shape):
    return shape == [4,3]

def is_44(shape):
    return shape == [4,4]

def is_321(shape):
    return shape == [3,2,1]

def is_33(shape):
    return shape == [3,3]


def is_good_P_1row(P, word, rev=False):
    if rev == False:
        return not has_rl_P_min(P, word) and P_Des(P, word) == [len(word)]
    elif rev == True:
        return not has_lr_P_max(P, word) and P_Des(P, word) == [len(word)]
    
def is_good_P_1row_B(P, word):
    return not has_rl_P_min(P, word) and P_Des(P, word) == [len(word)]
    
def is_good_P_1row_F(P, word, rev=False):
    return not has_lr_P_max(P, word) and P_Des(P, word) == [len(word)]

def is_good_P_hook(P, word, rev=False):
    sh = shape_of_word(P, word)
    arm = sh[0] - 1
    n = len(word)
    for i in range(n-arm):
        if is_good_P_1row(P, [word[i]]+word[n-arm:], rev=rev):
            return True
    return False

def is_good_P_2col(P, word):
    sh = shape_of_word(P, word)
    ell = len(sh)
    r = 0
    for k in range(ell, len(word)):
        while r < ell and is_P_compatible(P, word[r], word[k]):
            r += 1
        if r == ell: return False
        r += 1
    return True

def restriction_of_P(P):
    n = len(P)
    for i in range(1,n+1):
        yield deleting_i_from_P(P, i)

def deleting_i_from_P(P, i):
    n = len(P)
    deg = 0
    deleted_P = []
    for j in range(i-1):
        if P[j] >= i:
            deleted_P.append(P[j]-1)
            deg += 1
        else:
            deleted_P.append(P[j])
    for j in range(i, n):
        deleted_P.append(P[j]-1)
    return deleted_P, deg

def deleting_chain_from_P(P, chain):
    n = len(P)
    deg = 0
    deleted_P = list(P)
    chain = sorted(chain, reverse=True)
    for i in chain:
        deleted_P, d = deleting_i_from_P(deleted_P, i)
        deg += d
    return deleted_P, deg

def POSET(P):
    n = len(P)
    elements = [i for i in range(1,n+1)]
    relations = []
    for i in range(n):
        for j in range(P[i]+1, n+1):
            relations.append([i+1,j])
    return Poset((elements, relations))

def chains_in_P(P, length=None):
    n = len(P)
    chains = []
    if length == None:
        length = [i for i in range(n+1)]
    else:
        length = [length]
    for chain in POSET(P).chains():
        if len(chain) in length:
            chains.append(chain)
    return chains

def skewing_h_by_e(lamb, k):
    sym = 0
    length = len(lamb)
    for S in Combinations(length, k):
        mu = []
        for i in range(length):
            if i in S: mu.append(lamb[i]-1)
            else: mu.append(lamb[i])
        sym += h(sorted(mu,reverse=True))
    return sym

def skewing_h_by_p(lamb, k):
    sym = 0
    length = len(lamb)
    for i in range(length):
        mu = list(lamb)
        if mu[i] >= k:
            mu[i] -= k
            sym += h(sorted(mu, reverse=True))
    return sym

def elementary_vector(n, S, complement=False):
    vec = []
    for i in range(n):
        if (i in S and not complement) or (not i in S and complement): vec.append(1)
        else: vec.append(0)
    return vec

def PTab_from_word(P, word, rev=False):
    shape = shape_of_word(P, word, rev)
    if shape == None:
        print("It is not a P-tabluea")
        return False
    conj_shape = Partition(shape).conjugate()
    T = []
    a = 0
    for row in conj_shape:
        T.append([])
        for k in reversed(range(row)):
            T[-1].append(word[a+k])
        a += row
    return Tableau(T).conjugate()

def Tab_from_word(word, shape):
    conj_shape = Partition(shape).conjugate()
    T = []
    a = 0
    for row in conj_shape:
        T.append([])
        for k in reversed(range(row)):
            T[-1].append(word[a+k])
        a += row
    return Tableau(T).conjugate()

def verifier(P, word):
    T = PTab_from_word(P, word)
    if T == False: return False
    
    conditions = [condition1]
    for condition in conditions:
        if condition(P, T) == False:
            return False
    return True

def condition1(P, T):                 ## 가장 짧은 row의 길이를 l이라고 했을 때 (l=shape[-1]), 각 row의 길이 l짜리 prefix가 no rl P min 인가
    shape = T.shape()
    k = shape[-1]
    for row in T:
        if has_rl_P_min(P, row[:k]) == True:
            return False
    return True

def condition2(P, T):                 ## row 길이대로 tableau를 짜른 다음 짜른 각각의 piece에서의 row를 가져와서 no rl P min을 만들 수 있는 조합이 있는지 확인
    shape = T.shape()
    row_lengths = [0]
    for length in reversed(list(shape)):
        if length > row_lengths[-1]:
            row_lengths.append(length)
    for i in range(len(row_lengths)-1):
        length1 = row_lengths[i]
        length2 = row_lengths[i+1]
        words1 = [row[:length1] for row in T if len(row) >= length1]
        words2 = [row[length1:length2] for row in T if len(row) >= length2]
        if len(words1) <= len(words2) and length1 > 0:
            print("Something goes wrong!")
            return False
        
        chk1 = False
        for idx in permutations(range(len(words1)), len(words2)):
            chk2 = True
            for k in range(len(idx)):
                if has_rl_P_min(P, words1[idx[k]]+words2[k]) == True:
                    chk2 = False
                    break
            if chk2 == True:
                chk1 = True
                break
        if chk1 == False:
            return False
    return True

def condition3(P, T):                 ## 2row 라고 고정시켜놓고 shape 이 a, b 라고 하면, T[0], T[1]이 no rl P min 이거나 T[0][:b], T[1]+T[0][b:]이 no rl P min 이거나 (모든 경우 no P Desㅇㅇ)
    shape = T.shape()
    if len(shape) != 2: return False
    a, b = shape[0], shape[1]
    if has_rl_P_min(P, T[0]) == False and has_rl_P_min(P, T[1]) == False:
        return True
    if a > b:
        if has_rl_P_min(P, T[0][:b]) == False and has_rl_P_min(P, T[1]+T[0][b:]) == False and is_P_less(P, T[0][b], T[1][b-1]) == False:
            return True
    return False

def comb_to_shuffle(comb, A, B):
    iterA = iter(A)
    iterB = iter(B)
    return [next(iterA) if i in comb else next(iterB) for i in range(len(A) + len(B))]

def iter_shuffles(lists):
    if len(lists) == 1:
        yield lists[0]
    elif len(lists) == 2:
        for comb in itertools.combinations(range(len(lists[0]) + len(lists[1])), len(lists[0])):
            yield comb_to_shuffle(comb, lists[0], lists[1])
    else:
        length_sum = sum(len(word) for word in lists)
        for comb in itertools.combinations(range(length_sum), len(lists[0])):
            for shuffled in iter_shuffles(lists[1:]):
                yield comb_to_shuffle(comb, lists[0], shuffled)

def cluster_vertices(P):
    n = len(P)
    arr = [0 for i in range(n)]
    k = 0
    for i in range(1,len(P)):
        if P[i-1] != P[i]:
            for j in range(P[i-1], P[i]):
                arr[j] += i
            k += 1
        arr[i] += k
    vertices = [[1]]
    for i in range(1, len(P)):
        if arr[i-1] == arr[i]:
            vertices[-1].append(i+1)
        else:
            vertices.append([i+1])
    return vertices


def is_good_2row_based_on_conj(P, word, rev=False):
    shape = shape_of_word(P, word, rev=rev)
    if shape == None: return False
    word1 = []
    word2 = []
    word3 = []
    for i in range(shape[1]):
        word2.append(word[i*2])
        word1.append(word[i*2+1])
    for i in range(shape[1]*2, len(word)):
        word3.append(word[i])
    if is_good_P_1row(P, word1+word3, rev=rev) and is_good_P_1row(P, word2, rev=rev): return True
    if is_good_P_1row(P, word1, rev=rev) and is_good_P_1row(P, word2+word3, rev=rev): return True
    return False

def restricted_P_word(P, word):
    res_P = []
    res_word = []
    N = len(P)
    n = len(word)
    sorted_word = sorted(word)
    for i in range(n):
        j = i + 1
        while j < n:
            if P[sorted_word[i]-1] < sorted_word[j]:
                break
            j += 1
        res_P.append(j)
    for i in range(n):
        res_word.append(sorted_word.index(word[i])+1)
    return res_P, res_word

def is_good_2row_based_on_combination_of_hook_and_2col(P, word):
    shape = shape_of_word(P, word)
    if shape == None: return False
    if is_1row(shape): return is_good_P_1row(P, word)
    if not is_2row(shape):
        print("Error: The input is not 2row.")
        return False
    T = PTab_from_word(P, word)
    a = len(T[0])
    b = len(T[1])
    
    ## Check rightmost hook
    res_word = [T[1][b-1]] + list(T[0][b-1:a])
    res_P, res_word = restricted_P_word(P, res_word)
    if not is_good_P_hook(res_P, res_word): return False

    ## Check 2col
    for i in range(b-1):
        res_word = [T[1][i], T[0][i], T[1][i+1], T[0][i+1]]
        res_P, res_word = restricted_P_word(P, res_word)
        if not is_good_P_2col(res_P, res_word): return False
    return True

def find_counter_example(P, word, shape_checker, good_checker):
    N = len(word)
    words = words_from_orbit(P, word)
    sym = h(F_gamma(P, words).to_symmetric_function())
    cnts = dict()
    for lamb in Partitions(N): cnts[lamb] = 0
    for word in words:
        shape = shape_of_word(P, word)
        if shape == None: continue
        if shape_checker(shape) and good_checker(P, word):
            cnts[shape] += 1
    result = []
    for lamb in Partitions(N):
        if shape_checker(lamb) == False: continue
        if cnts[lamb] != sym.coefficient(lamb):
            result.append(dict())
            result[-1]["P"] = P
            result[-1]["word"] = word
            result[-1]["shape"] = convert_Integer_to_int(list(lamb))
            result[-1]["number_of_good"] = convert_Integer_to_int(cnts[lamb])
            result[-1]["coeff_of_lamb"] = convert_Integer_to_int(int(sym.coefficient(lamb)))
    return result, words

def convert_Integer_to_int(data):
    if type(data) == Integer:
        return int(data)
    if type(data) == list or type(data) == tuple:
        converted_data = []
        for a in data:
            converted_data.append(int(a))
        if type(data) == tuple: return tuple(converted_data)
        return converted_data
    return data

def update_DB(N, good_type):
    DB_FILE = DB_DATA[good_type]["PATH"]
    with open(DB_FILE, "r") as f:
        counter_examples = json.load(f)
    if f"{N}" in counter_examples.keys():
        print(f"The data for {N} already exist in DB.")
        return
    
    good_checker = DB_DATA[good_type]['good_checker']
    
    counter_examples[f"{N}"] = []
    for P in generate_UIO(N, connected=True):
        word_list = []
        P = convert_Integer_to_int(P)
        for word in iter_shuffles(cluster_vertices(P)):
            word = convert_Integer_to_int(list(word))
            if word in word_list: continue
            result, words = find_counter_example(P, word, any_shape, good_checker)
            word_list.extend(words)
            counter_examples[f"{N}"].extend(result)

    with open(DB_FILE, "w") as f:
        json.dump(counter_examples, f)
    print(f"The update for {N} has succeeded.")

def load_counter_example(good_type, N='all'):
    DB_FILE = DB_DATA[good_type]["PATH"]
    with open(DB_FILE, "r") as f:
        counter_examples = json.load(f)
    if N == 'all':
        return counter_examples
    if f'{N}' in counter_examples.keys():
        return counter_examples[f'{N}']
    raise Exception(f"There is no data for {N}")
    
def print_counter_example(counter_example):
    P, word = counter_example["P"], counter_example["word"]
    words = words_from_orbit(P, word)
    sym = h(F_gamma(P, words).to_symmetric_function())
    print(f"{P}, {word}, {counter_example['shape']}")
    print(f"{sym}")
    print(f"{counter_example['number_of_good']} {counter_example['coeff_of_lamb']}")
    print("="*50)

def analyze_counter_example(counter_example, good_checker, good_only=True, dominated_partion=True):
    P, word = counter_example["P"], counter_example["word"]
    words = words_from_orbit(P, word)
    shape = Partition(counter_example['shape'])
    sym = h(F_gamma(P, words).to_symmetric_function())

    print(f"{P}, {word}, {shape}")
    print(f"{sym}")
    print(f"{s(sym)}")
    print(f"# of goods = {counter_example['number_of_good']}, coeff of {shape} = {counter_example['coeff_of_lamb']}")
    print("="*23)
    Tabs = []
    for word in words:
        T_shape = shape_of_word(P, word)
        if T_shape != None:
            if (good_only == False or good_checker(P, word) == True) and ((dominated_partion == False and Partition(T_shape) == shape) or Partition(T_shape) in shape.dominated_partitions()):
                Tabs.append((T_shape, word))
    Tabs.sort()
    for _, word in Tabs:    
        PTab_from_word(P, word).pp()
        print(good_checker(P, word))
        print("="*23)
    print(" ")

def get_orbits(P, primitive=False):
    N = len(P)
    orbits = []
    word_list = []
    if primitive == True:
        iter_words = iter_shuffles(cluster_vertices(P))
    else: iter_words = Permutations(N)
    for word in iter_words:
        word = list(word)
        if word in word_list: continue
        words = words_from_orbit(P, word)
        orbits.append(words)
        word_list.extend(words)
    return orbits

def get_maximal_P_paths(P, paths=None, path=None, letters='start'):
    n = len(P)
    conj_P = list(reversed(P_conjugate(P)))
    if letters == 'start':
        paths = []
        for i in range(n):
            for j in range(i+1, n):
                if conj_P[i] == conj_P[j]:
                    path = [i+1, j+1]
                    get_maximal_P_paths(P, paths, path, [k+1 for k in range(P[i],P[j])])
        return paths
    elif letters == []:
        paths.append(list(path))
    else:
        b = path[-1]
        for c in letters:
            path2 = list(path+[c])
            get_maximal_P_paths(P, paths, path2, [k+1 for k in range(P[b-1],P[c-1])])

def index_row_number(P, word, paths):
    shape = shape_of_word(P, word)
    if shape == None:
        raise Exception("The input is not a P-tableau.")

    N = len(word)
    indices = []
    row_num = [-1 for k in range(N+1)]
    p = 0
    for i, a in enumerate(conjugate(shape)):
        for j in reversed(range(a)):
            row_num[word[p]] = j + 1
            p += 1
    for path in paths:
        indices.append([])
        for a in path:
            indices[-1].append(row_num[a])
    return indices

def index_column_number(P, word, paths):
    shape = shape_of_word(P, word)
    if shape == None:
        raise Exception("The input is not a P-tableau.")

    N = len(word)
    indices = []
    col_num = [-1 for k in range(N+1)]
    p = 0
    for i, a in enumerate(conjugate(shape)):
        for j in range(a):
            col_num[word[p]] = i + 1
            p += 1
    for path in paths:
        indices.append([])
        for a in path:
            indices[-1].append(col_num[a])
    return indices


########################################
############## criterions ##############
########################################

def check_inductive_disconnectedness_criterion(P, word, rev=False):
    shape = shape_of_word(P, word, rev=rev)
    conj = conjugate(shape)
    k = len(word)
    for c in reversed(range(shape[0])):
        k -= conj[c]
        res_P, res_word = restricted_P_word(P, word[k:])
        if check_disconnectedness_criterion(res_P, res_word, rev=rev) == False:
            return False
    return True

def check_inductive_disconnectedness_criterion_forward(P, word, rev=False):
    shape = shape_of_word(P, word, rev=rev)
    conj = conjugate(shape)
    k = 0
    for c in range(shape[0]):
        k += conj[c]
        res_P, res_word = restricted_P_word(P, word[:k])
        if check_disconnectedness_criterion(res_P, res_word, rev=rev) == False:
            return False
    return True

def check_disconnectedness_criterion(P, word, rev=False):
  shape = shape_of_word(P, word, rev=rev)
  conj = conjugate(shape)
  components = split_into_connected_components(P)
  index = index_set_from_connected_components(components)

  cnts = [[] for comp in components]
  res_words = [[] for comp in components]

  k = 0
  for i in range(len(conj)):
    for cnt in cnts: cnt.append(0)
    for j in range(conj[i]):
      cnts[index[word[k]]][-1] += 1
      res_words[index[word[k]]].append(word[k])
      k += 1
  chk = True
  for cnt in cnts:
    if is_non_increasing(cnt) == False:
      return False
  for i in range(len(components)):
    res_P, res_word = restricted_P_word(P, res_words[i])
    res_shape = shape_of_word(res_P, res_word, rev=rev)
    if res_shape == None or Partition(cnts[i]).conjugate() != Partition(res_shape):
      return False
  return True

def check_2row_each_row_connected(P, word, rev=False):
    shape = shape_of_word(P, word)
    T = PTab_from_word(P, word)
    word1 = list(T[0][:shape[1]])
    word2 = list(T[1])
    word3 = list(T[0][shape[1]:])
    if is_good_P_1row(P, word1+word3, rev) and is_good_P_1row(P, word2, rev): return True
    if is_good_P_1row(P, word1, rev) and is_good_P_1row(P, word2+word3, rev): return True
    return False

def is_connected(P):
    for i in range(len(P)-1):
        if P[i] == i+1:
            return False
    return True

def check_all_row_connected(P, word, direction='B'):
    if direction == 'B': row_checker = is_good_P_1row_B
    elif direction == 'F': row_checker = is_good_P_1row_F
    else:
        print("Check the parameter for 'direction'")
        return

    T = PTab_from_word(P, word)
    shape = shape_of_word(P, word)
    shape_of_pieces = []
    pieces = [[] for i in range(len(shape))]
    prev = 0
    for k in reversed(range(len(shape))):
        if shape[k] > prev:
            shape_of_pieces.append(k+1)
            for i in range(k+1):
                pieces[i].append(T[i][prev:shape[k]])
            prev = shape[k]
    base_words = []
    for i in range(len(pieces)):
        base_words.append(list(pieces[i][0]))
    if concatenating(P, shape_of_pieces, list(range(shape_of_pieces[0])), 1, pieces, base_words, row_checker) == True:
        return True
    return False

def check_2row_connected_forward_with_additional_conditions(P, word):
    if check_all_row_connected(P, word, direction='F') == False: return False
    shape = shape_of_word(P, word)
    

def concatenating(P, shape_of_pieces, prev_block, k, pieces, prev_concatenated_words, good_1row_checker):
    if k == len(shape_of_pieces):
        for word in prev_concatenated_words:
            if good_1row_checker(P, word) == False:
                return False
        return True
    for block in itertools.combinations(prev_block, shape_of_pieces[k]):
        concatenated_words = deepcopy(prev_concatenated_words)
        for i, p in enumerate(block):
            concatenated_words[p].extend(pieces[i][k])
        if concatenating(P, shape_of_pieces, block, k+1, pieces, concatenated_words, good_1row_checker):
            return True
    

def split_into_connected_components(P):
  components = [[]]
  for i in range(len(P)-1):
    components[-1].append(i+1)
    if P[i] == i+1:
      components.append([])
  components[-1].append(len(P))
  return components

def index_set_from_connected_components(components):
  N = max(max(component) for component in components)
  index = [-1 for i in range(N+1)]
  for i, component in enumerate(components):
    for k in component:
      index[k] = i
  return index

def conjugate(lamb):
  conj = []
  for i in range(1, lamb[0]+1):
    cnt = 0
    for part in lamb:
      if part >= i:
        cnt += 1
    conj.append(cnt)
  return conj

def is_non_increasing(seq):
  for i in range(1, len(seq)):
    if seq[i-1] < seq[i]:
      return False
  return True

def check_pattern(P, word, pattern):
    res_P, res_word = restricted_P_word(P, word)
    if res_P != pattern[0]: return False, None
    if pattern[1][0] == res_word: target_word = pattern[1][1]
    elif pattern[1][1] == res_word: target_word = pattern[1][0]
    else: return False, None
    sorted_word = list(word)
    sorted_word.sort()
    recovered_word = []
    for a in target_word:
        recovered_word.append(sorted_word[a-1])
    return True, recovered_word


def flippable_criterion(P, word):
    shape = shape_of_word(P, word)
    conj = conjugate(shape)
    cols = []
    k = 0
    for i in range(shape[0]):
        cols.append(word[k:k+conj[i]])
        k += conj[i]
    k = 0
    for i in range(shape[0]-1):
        if len(cols[i]) == 1: break
        combined = []
        for a in cols[i]:
            combined.append((a, 0))
        for a in cols[i+1]:
            combined.append((a, 1))
        combined.sort(reverse=True)

        p = 0
        while p < len(combined):
            q = p + 1
            while q < len(combined):
                if is_P_compatible(P, combined[q-1][0], combined[q][0]):
                    break
                q += 1
            if (q - p) % 2 == 0 or combined[p][1] == 0:
                p = q
                continue
            col1 = []
            col2 = []
            for j, (a, idx) in enumerate(combined):
                if j >= p and j < q:
                    idx = 1 - idx
                if idx == 0: col1.append(a)
                elif idx == 1: col2.append(a)
            if shape_of_word(P, word[:k]+col1+col2+word[k+conj[i]+conj[i+1]:]) == conjugate(conj[:i]+[conj[i]+1,conj[i+1]-1]+conj[i+2:]):
                return False
            p = q
        
        k += conj[i]
    return True

def combine_backward_connected_and_flippable(P, word):
    return check_inductive_disconnectedness_criterion(P, word) and flippable_criterion(P, word)






######################################################################################################
###################################### For Composition Tableaux ######################################
######################################################################################################

from copy import deepcopy

def CompTab(P):
    n = len(P)
    result = []
    for comp in Compositions(n):
        result += CompTab_sh(P, comp)
    return result

def CompTab_conj(P):
    n = len(P)
    result = 0
    for comp in Compositions(n):
        sh = sorted(comp, reverse=True)
        result += len(CompTab_sh(P, comp)) * s(sh)
    return result

def CompTab_conj_qversion(P):
    n = len(P)
    result = 0
    for comp in Compositions(n):
        sh = sorted(comp, reverse=True)
        for T in CompTab_sh(n, P, comp):
            result += (q**get_inv_word(n,P,ComT_word(n,T))) * s(sh)
    return result

def CompTab_sh(P, sh):   ## ex) P=[2,4,4,5,5], sh=[1,1,2,1]
    n = len(P)
    chk = [0 for i in range(n+1)]
    m = max(sh)
    P = [0]+P+[n+1]
    Tab = [[0 for i in range(m)] for j in range(len(sh))]
    result = []

    recur_CompTab_sh(n, P, sh, Tab, chk, 0, 0, result)

    return result

def recur_CompTab_sh(n, P, sh, Tab, chk, k, l, result):
    if k >= len(sh):
        recur_CompTab_sh(n, P, sh, Tab, chk, 0, l+1, result)
        return
    if l >= max(sh):
        result.append(deepcopy(Tab))
        return
    if l >= sh[k]:                                                                             ## augmentation condition
        j = 0
        while j < k:
            if Tab[j][l] == n+1:
                j += 1
                continue
            if is_P_less(P[1:], Tab[j][l], Tab[k][l-1]) == 0:                                      ## Triple rule
                break
            j += 1
        if j < k:
            return
        Tab[k][l] = n+1
        recur_CompTab_sh(n, P, sh, Tab, chk, k+1, l, result)
        return

    for i in range(1,n+1):
        if chk[i]:
            continue
        if l == 0:
            if k == 0:
                chk[i] = 1
                Tab[k][l] = i
                recur_CompTab_sh(n, P, sh, Tab, chk, k+1, l, result)
                chk[i] = 0
            else:
                if is_P_less(P[1:], Tab[k-1][l], i):                                                 ## first column condition
                    chk[i] = 1
                    Tab[k][l] = i
                    recur_CompTab_sh(n, P, sh, Tab, chk, k+1, l, result)
                    chk[i] = 0
        else:
            if is_P_less(P[1:], i, Tab[k][l-1]) == 1:                                                ## row condition
                continue
            j = 0
            while j < k:
                if is_P_less(P[1:], Tab[j][l], i) + is_P_less(P[1:], i, Tab[j][l]) == 0:                 ## column independence
                    break
                if is_P_less(P[1:], Tab[j][l], Tab[k][l-1]) + is_P_less(P[1:], i, Tab[j][l]) == 0:    ## Triple rule
                    break
                j += 1
            if j == k:
                chk[i] = 1
                Tab[k][l] = i
                recur_CompTab_sh(n, P, sh, Tab, chk, k+1, l, result)
                chk[i] = 0

def get_shape(n, T):
    comp = []
    for i in range(len(T)):
        comp.append(0)
        for j in range(len(T[i])):
            if T[i][j] > n:
                break
            comp[i] += 1
    comp.sort(reverse=True)
    return comp

def ComT_word(n, T):
    word = []
    for i in range(len(T[0])):
        for j in range(len(T)):
            if T[j][i] <= n:
                word.append(T[j][i])
    return word

def gather_ComT_along_orbit(P, word):
    n = len(P)
    words = words_from_orbit(P, word)
    ComT = CompTab(P)
    result = []
    
    for T in ComT:
        if ComT_word(n,T) in words:
            result.append(T)
    return result

def conj_gather_ComT_along_heaps(P, word):
    n = len(P)
    result = 0
    ComT = gather_ComT_along_orbit(P, word)
    for T in ComT:
        result += s(get_shape(n, T))
    return result
    
def is_no_P_des_no_P_lrmax(n, P, row):
    for i in range(1,len(row)):
        if row[i] > n:
            break
        if is_P_less(P, row[i], row[i-1]):
            return 0
        chk = 0
        for j in range(i):
            if is_P_less(P, row[j], row[i]) == 0:
                chk = 1
                break
        if chk == 0:
            return 0
    return 1




#############################################
################## DB Data ##################
#############################################

DB_DATA = {
    "all_row_connected_B":
        {"PATH": '/Users/hwangbyunghak/Documents/Sage/e-positivity/DB/counter_examples_all_row_connected_B.json',
         "good_checker": check_all_row_connected,
        },
    "inductively_connected_B":
        {"PATH": '/Users/hwangbyunghak/Documents/Sage/e-positivity/DB/counter_examples_inductively_connected_B.json',
         "good_checker": check_inductive_disconnectedness_criterion,
        },
    "flippble":
        {"PATH": '/Users/hwangbyunghak/Documents/Sage/e-positivity/DB/counter_examples_flippable.json',
         "good_checker": combine_backward_connected_and_flippable,
        },
}

