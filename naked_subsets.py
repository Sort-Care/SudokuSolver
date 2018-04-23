from utils import *
import itertools

def naked_subsets(csp, var, value, assignment, removals = None):

    """find naked subsets of var

    Note that naked subsets' size could be any number in range [2,3,...9]

    Strength is for the upper bound of naked subsets' size

    """



    for strength in range(2,5):

        prune_row_naked(csp, removals, strength, assignment)

        prune_col_naked(csp, removals, strength, assignment)

        prune_block_naked(csp, removals, strength, assignment)



              

    return True



def prune_row_naked(csp, removals, strength, assignment):

    for i in range(9):

        row_vars = get_row(csp, i)

        row_vars = delete_asgned(csp, row_vars, assignment)

        combs = get_combination_vars(row_vars, strength)

        for t in combs:

            vlist = list(t) # get combination variable list

            if check_naked(csp, vlist):# check if this combination is a naked list

                # variables that need to be pruned

                prune_list = [v for v in row_vars if v not in vlist]

                # values that need to be pruned

                p_domain = get_domain_set(csp, vlist)

                prune_domain(csp, p_domain, prune_list, removals)





def prune_col_naked(csp, removals, strength, assignment):

    for i in range(9):

        col_vars = get_col(csp, i)

        col_vars = delete_asgned(csp, col_vars, assignment)

        combs = get_combination_vars(col_vars, strength)

        for t in combs:

            vlist = list(t) # get combination variable list

            if check_naked(csp, vlist):# check if this combination is a naked list

                # variables that need to be pruned

                prune_list = [v for v in col_vars if v not in vlist]

                # values that need to be pruned

                p_domain = get_domain_set(csp, vlist)

                prune_domain(csp, p_domain, prune_list, removals)



def prune_block_naked(csp, removals, strength, assignment):

    for i in range(9):

        block_vars = get_block(csp, i)

        block_vars = delete_asgned(csp, block_vars, assignment)

        combs = get_combination_vars(block_vars, strength)

        for t in combs:

            vlist = list(t) # get combination variable list

            if check_naked(csp, vlist):# check if this combination is a naked list

                # variables that need to be pruned

                prune_list = [v for v in block_vars if v not in vlist]

                # values that need to be pruned

                p_domain = get_domain_set(csp, vlist)

                prune_domain(csp, p_domain, prune_list, removals)

                



def get_combination_vars(vlist, size):

    return list(combinations(vlist, size))



def delete_asgned(csp, vlist, assignment):

    for v in vlist:

        if v in assignment:

            vlist.remove(v)

    return vlist



def get_row(csp, row):

    return [row * 9 + v for v in range(9)]



def get_col(csp, col):

    return [v * 9 + col for v in range(9)]



def get_block(csp, block):

    origin = [0,1,2,9,10,11,18,19,20]

    r,c = divmod(block, 3)

    adding = r * 27 + c * 3

    return [v+adding for v in origin]



def get_domain_set(csp, varlist):

    domain_set = set()

    for v in varlist:

        domain_set.update(csp.curr_domains[v])

    return domain_set



def prune_domain(csp, domains, vlist, removals):

    for v in vlist:

        for val in csp.curr_domains[v]:

            if val in domains:

                csp.prune(v, val, removals)





def check_naked(csp, varlist):

    list_size = len(varlist)

    domain_set = set()

    for v in varlist:

        domain_set.update(csp.curr_domains[v])



    if list_size == len(domain_set):

        return True

    return False





def is_peer(v1, v2):

    """is v1 v2 of same row or column or block

    return -1: not peers  0:same  1: row   2: column  3: block  4: row and block  5: col and block

    """

    row_v1, col_v1 = divmod(v1, 9)

    row_v2, col_v2 = divmod(v2, 9)

    if row_v1 == row_v2 and col_v1 == col_v2:

        return 0 # same variable

    

    elif row_v1 == row_v2 and col_v1 != col_v2:

        if abs(row_v1 - row_v2) < 3: # row and block

            return 4

        else: # row

            return 1

        

    elif row_v1 != row_v2 and col_v1 ==  col_v2:

        if abs(col_v1 - col_v2) < 3: # col and block

            return 5

        else:

            return 2

        

    elif abs(row_v1 - row_v2) < 3 and abs(col_v1 - col_v2) < 3: # block

        return 3



    else:

        return -1

    





def get_peers(csp, var, peertype = 1):

    if peertype == 1: # row peers

        var_peers = get_row_peers(csp, var)

    elif peertype == 2: # col peers

        var_peers = get_col_peers(csp, var)

    elif peertype == 3: # block peers

        var_peers = get_block_peers(csp, var)

    elif peertype == 4: # row and block peers

        row_peers = get_row_peers(csp, var)

        block_peers = get_block_peers(csp, var)

        var_peers = list(set().union(row_peers, block_peers))

    elif peertype == 5: # col and block peers

        col_peers = get_col_peers(csp, var)

        block_peers = get_block_peers(csp, var)

        var_peers = list(set().union(col_peers, block_peers))

    elif peertype == 6: # all peers

        row_peers = get_row_peers(csp, var)

        col_peers = get_col_peers(csp, var)

        block_peers = get_block_peers(csp, var)

        var_peers = list(set().union(row_peers, col_peers, block_peers))

        

    return var_peers



def get_row_peers(csp, var):

    peers = []

    r, l = divmod(var, 9)

    for i in range(9):

        if i != l:

            peer = r * 9 + i

            # if peer is not assigned

            if peer not in assignment:

                peers.append(peer)

            

    return peers



def get_col_peers(csp, var):

    peers = []

    r, l = divmod(var, 9)

    for j in range(9):

        if j!= r:

            peer = 9 * j + l

            if peer not in assignment:

                peers.append(peer)



    return peers



def get_block_peers(csp, var):

    peers = []

    r, l = divmod(var, 9)

    rr = r % 3 # row remainder

    rc = l % 3 # column remainder

    offset = [0,1,2]

    row_idxes = [v - rr for v in offset]

    column_idxes = [v - rc for v in offset]

    for x, y in [(x, y) for x in row_idxes for y in column_idxes]:

        pr = r + x

        pc = l + y

        cor = pr * 9 + pc

        if cor not in assignment:

            peers.append(cor)

    return peers
