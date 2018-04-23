"""CSP (Constraint Satisfaction Problems) problems and solvers. (Chapter 6)."""

from utils import argmin_random_tie, count, first, FIFOQueue

from collections import defaultdict, deque
from functools import reduce
from naked_subsets import naked_subsets

import itertools
import statistics
import re
import random
import copy


class CSP(object):
    """This class describes finite-domain Constraint Satisfaction Problems.
    A CSP is specified by the following inputs:
        variables   A list of variables; each is atomic (e.g. int or string).
        domains     A dict of {var:[possible_value, ...]} entries.
        neighbors   A dict of {var:[var,...]} that for each variable lists
                    the other variables that participate in constraints.
        constraints A function f(A, a, B, b) that returns true if neighbors
                    A, B satisfy the constraint when they have values A=a, B=b
    In the textbook and in most mathematical definitions, the
    constraints are specified as explicit pairs of allowable values,
    but the formulation here is easier to express and more compact for
    most cases. (For example, the n-Queens problem can be represented
    in O(n) space using this notation, instead of O(N^4) for the
    explicit representation.) In terms of describing the CSP as a
    problem, that's all there is.
    However, the class also supports data structures and methods that help you
    solve CSPs by calling a search function on the CSP. Methods and slots are
    as follows, where the argument 'a' represents an assignment, which is a
    dict of {var:val} entries:
        assign(var, val, a)     Assign a[var] = val; do other bookkeeping
        unassign(var, a)        Do del a[var], plus other bookkeeping
        nconflicts(var, val, a) Return the number of other variables that
                                conflict with var=val
        curr_domains[var]       Slot: remaining consistent values for var
                                Used by constraint propagation routines.
    The following methods are used only by graph_search and tree_search:
        actions(state)          Return a list of actions
        result(state, action)   Return a successor of state
        goal_test(state)        Return true if all constraints satisfied
    The following are just for debugging purposes:
        nassigns                Slot: tracks the number of assignments made
        display(a)              Print a human-readable representation
    """

    def __init__(self, variables, domains, neighbors, constraints):
        """Construct a CSP problem. If variables is empty, it becomes domains.keys()."""
        variables = variables or list(domains.keys())

        self.variables = variables
        self.domains = domains
        self.neighbors = neighbors
        self.constraints = constraints
        self.initial = ()
        self.curr_domains = None
        self.nassigns = 0

    def assign(self, var, val, assignment):
        """Add {var: val} to assignment; Discard the old value if any."""
        assignment[var] = val
        self.nassigns += 1

    def unassign(self, var, assignment):
        """Remove {var: val} from assignment.
        DO NOT call this if you are changing a variable to a new value;
        just call assign for that."""
        if var in assignment:
            del assignment[var]

    def nconflicts(self, var, val, assignment):
        """Return the number of conflicts var=val has with other variables."""
        # Subclasses may implement this more efficiently
        def conflict(var2):
            #if var2 in assignment:
               # print('var %d :val %d, var2 %d: val %d' % (var, val, var2, assignment[var2]))
               # print(var2 in assignment and
               #         not self.constraints(var, val, var2, assignment[var2]))

            return (var2 in assignment and
                    not self.constraints(var, val, var2, assignment[var2]))
        return count(conflict(v) for v in self.neighbors[var])

    def display(self, assignment):
        """Show a human-readable representation of the CSP."""
        # Subclasses can print in a prettier way, or display with a GUI
        print('CSP:', self, 'with assignment:', assignment)

    # These are for constraint propagation

    def support_pruning(self):
        """Make sure we can prune values from domains. (We want to pay
        for this only if we use it.)"""
        if self.curr_domains is None:
            self.curr_domains = {v: list(self.domains[v]) for v in self.variables}

    def suppose(self, var, value):
        """Start accumulating inferences from assuming var=value."""
        self.support_pruning()
        removals = [(var, a) for a in self.curr_domains[var] if a != value]
        self.curr_domains[var] = [value]
        return removals

    def prune(self, var, value, removals):
        """Rule out var=value."""
        self.curr_domains[var].remove(value)
        if removals is not None:
            removals.append((var, value))

    def choices(self, var):
        """Return all values for var that aren't currently ruled out."""
        return (self.curr_domains or self.domains)[var]

    def infer_assignment(self):
        """Return the partial assignment implied by the current inferences."""
        self.support_pruning()
        return {v: self.curr_domains[v][0]
                for v in self.variables if 1 == len(self.curr_domains[v])}

    def restore(self, removals):
        """Undo a supposition and all inferences from it."""
        for B, b in removals:
            self.curr_domains[B].append(b)

# ______________________________________________________________________________
# Constraint Propagation with AC-3


def AC3(csp, queue=None, removals=None):
    """[Figure 6.3]"""
    if queue is None:
        queue = [(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]]
    csp.support_pruning()
    while queue:
        (Xi, Xj) = queue.pop()
        if revise(csp, Xi, Xj, removals):
            if not csp.curr_domains[Xi]:
                return False
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.append((Xk, Xi))
    return True


def revise(csp, Xi, Xj, removals):
    """Return true if we remove a value."""
    revised = False
    for x in csp.curr_domains[Xi][:]:
        # If Xi=x conflicts with Xj=y for every possible y, eliminate Xi=x
        if all(not csp.constraints(Xi, x, Xj, y) for y in csp.curr_domains[Xj]):
            csp.prune(Xi, x, removals)
            revised = True
    return revised

def confined_row(csp, variables, candidate, box):
    """Decide if a candidate in a box is confined in a row"""
    v = set()
    for variable in variables:
        if candidate in csp.curr_domains[variable]:
            v.add(variable//csp.col)

    if len(v) == 1:
        return v.pop()
    return -1

def confined_col(csp, variables, candidate, box):
    """Decide if a candidate in a box is confined in a column"""
    v = set()
    for variable in variables:
        if candidate in csp.curr_domains[variable]:
            v.add(variable%csp.col)

    if len(v) == 1:
        return v.pop()
    return -1

def confined_box(csp, variables, candidate, box):
    """Decide if a candidate in a box is confined in this box"""
    pass


# ______________________________________________________________________________
# CSP Backtracking Search

# Variable ordering


def first_unassigned_variable(assignment, csp):
    """The default variable order."""
    return first([var for var in csp.variables if var not in assignment])


def mrv(assignment, csp):
    """Minimum-remaining-values heuristic."""
    return argmin_random_tie(
        [v for v in csp.variables if v not in assignment],
        key=lambda var: num_legal_values(csp, var, assignment))


def num_legal_values(csp, var, assignment):
    if csp.curr_domains:
        return len(csp.curr_domains[var])
    else:
        return count(csp.nconflicts(var, val, assignment) == 0
                     for val in csp.domains[var])

# Value ordering


def unordered_domain_values(var, assignment, csp):
    """The default value order."""
    return csp.choices(var)


def lcv(var, assignment, csp):
    """Least-constraining-values heuristic."""
    return sorted(csp.choices(var),
                  key=lambda val: csp.nconflicts(var, val, assignment))

# Inference


def no_inference(csp, var, value, assignment, removals):
    return True


def forward_checking(csp, var, value, assignment, removals):
    """Prune neighbor values inconsistent with var=value."""
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
            if not csp.curr_domains[B]:
                return False
    return True


def mac(csp, var, value, assignment, removals):
    """Maintain arc consistency."""
    return AC3(csp, [(X, var) for X in csp.neighbors[var]], removals)

def hidden_single(csp, variable, value, assignment, removals):
    """Find hidden singles in the Sudoku puzzle"""
    csp.support_pruning()
    queue = [var for var in csp.variables if var not in assignment]
    while queue:
        var = queue.pop()
        neighbors = [neighbor for neighbor in csp.neighbors[var]]
        for val in csp.curr_domains[var]:
            hidden = True
            for neighbor in neighbors:
                if val in csp.curr_domains[neighbor]:
                    hidden = False
                    break
            if hidden and len(csp.curr_domains[var]) > 1:
                excludes = [ex for ex in csp.curr_domains[var] if ex != val]
                for exclude in excludes:
                    csp.prune(var, exclude, removals)
                for neighbor in neighbors:
                    if neighbor not in queue and neighbor not in assignment:
                        queue.append(neighbor)
                break
    return True

def locked_candidates(csp, var, val, assignment, removals):
    """Find locked candidates (Pointing & Claiming)"""
    for box in [(x, y) for x in range(3) for y in range(3)]:
        variables = set([int(csp.col*(3*box[0]+i)+(3*box[1]+j)) for i in range(3) for j in range(3)])
        variables -= set(assignment)
        candidates = set()
        for variable in variables:
            candidates |= set(csp.curr_domains[variable])
        
        for candidate in candidates:
            row = confined_row(csp, variables, candidate, box)
            col = confined_col(csp, variables, candidate, box)
            if row >= 0:
                for j in range(csp.col):
                    neighbor = int(csp.col*row + j)
                    if neighbor not in variables and candidate in csp.curr_domains[neighbor]:
                        csp.prune(neighbor, candidate, removals)
                        if not csp.curr_domains[neighbor]:
                            return False
            if col >= 0:
                for i in range(csp.row):
                    neighbor = int(csp.col*i + col)
                    if neighbor not in variables and candidate in csp.curr_domains[neighbor]:
                        csp.prune(neighbor, candidate, removals)
                        if not csp.curr_domains[neighbor]:
                            return False
            #if confined_box(csp, candidate, box):
            #    pass
    return True
    
def waterfall(csp, var, val, assignment, removals):
    """
    Apply a waterfall of inferences
    Add whatever inference you like into all_inferences
    The waterfall will stop until no more effects incurr
    """
    all_inferences = [hidden_single]
    inferences = FIFOQueue(items=all_inferences)
    while inferences:
        inference = inferences.pop()
        tmp = removals.copy()
        if not inference(csp, var, val, assignment, removals):
            return False
        if tmp != removals:
            for next_inference in all_inferences:
                if next_inference != inference:
                    inferences.append(next_inference)
    return True


# The search, proper


def backtracking_search(csp, assignment={},
                        select_unassigned_variable=first_unassigned_variable,
                        order_domain_values=unordered_domain_values,
                        inference=no_inference):
    """[Figure 6.5]"""

    guess = 0

    def backtrack():
        if len(assignment) == len(csp.variables):
            return assignment
        var = select_unassigned_variable(assignment, csp)
        #print ('var: %d, assign: %d\n' % (var, len(assignment)))
        #print (csp.curr_domains)
        nonlocal guess 
        guess += len((csp.curr_domains or csp.domains)[var])-1
        for value in order_domain_values(var, assignment, csp):
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals):
                    result = backtrack()
                    if result is not None:
                        return result
                csp.restore(removals)
        csp.unassign(var, assignment)
        return None

    result = backtrack()
    print ("\nguesses took: %d" % guess)
#    assert result is None
    return result




def backtracking_search_guess(csp, assignment={},
                              select_unassigned_variable=first_unassigned_variable,
                              order_domain_values=unordered_domain_values,
                              inference=no_inference,
                              inferlist = []):
    """[Figure 6.5]"""

    guess = 0

    def backtrack():
        if len(assignment) == len(csp.variables):
            return assignment
        var = select_unassigned_variable(assignment, csp)
        #print ('var: %d, assign: %d\n' % (var, len(assignment)))
        #print (csp.curr_domains)
        nonlocal guess 
        guess += len((csp.curr_domains or csp.domains)[var])-1
        for value in order_domain_values(var, assignment, csp):
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals, inferlist):
                    result = backtrack()
                    if result is not None:
                        return result
                csp.restore(removals)
        csp.unassign(var, assignment)
        return None

    result = backtrack()
    return guess


def waterfall_levels(csp, var, val, assignment, removals, inferlist):
    """
    Apply a waterfall of inferences
    Add whatever inference you like into all_inferences
    The waterfall will stop until no more effects incurr
    """
    all_inferences = inferlist
    inferences = FIFOQueue(items=all_inferences)
    while inferences:
        inference = inferences.pop()
        tmp = removals.copy()
        if not inference(csp, var, val, assignment, removals):
            return False
        if tmp != removals:
            for next_inference in all_inferences:
                if next_inference != inference:
                    inferences.append(next_inference)
    return True


# ______________________________________________________________________________
# Sudoku

class Sudoku(CSP):
    """
    Author: Haoyu Ji, Hanwen Xiong
    This is a class for constructing Sudoku problem.
    Sudoku world is a 3x3 boxes each containing 3x3 cells.
    List xxx holds 81 variables for each cell,
    dict xxx holds 81 keys whose values correspond to its domains.
    """

    def __init__(self):
        self.row = 9
        self.col = 9
        self.num_vars = 81

        variables = list(range(self.num_vars))
        domains = {var: list(range(1, 10)) for var in range(self.num_vars)}
        neighbors = {var: [] for var in range(self.num_vars)}
        for var in variables:
            r, l = divmod(var, self.col)
            bx, by = (r//3, l//3)
            neighbors[var] += [nr*self.col+l for nr in range(self.row)]
            neighbors[var] += [r*self.col+nl for nl in range(self.col)]
            for i in range(3):
                for j in range(3):
                    neighbors[var].append(int(self.col*(3*bx+i)+(3*by+j)))
            neighbors[var] = list(set(neighbors[var]))
            neighbors[var].remove(var)

        super().__init__(variables, domains, neighbors, self.sudoku_constraints)

    def read_sudoku(self, filename):
        """
        Read Sudoku from file with format:
        - 1 9 - - - - - -
        - - 8 - - 3 - 5 -
        - 7 - 6 - - - 8 -
        - - 1 - - 6 8 - 9
        8 - - - 4 - - - 7
        9 4 - - - - - 1 -
        - - - - - 2 - - -
        - - - - 8 - 5 6 1
        - - 3 7 - - - 9 -
        """
        with open(filename) as f:
            for i in range(self.num_vars):
                while True:
                    c = f.read(1)
                    if c != '\n' and c != '\r' and c != ' ':
                        break

                if c != '-':
                    digit = int(c)
                    self.domains[i] = [digit]

    def print_sudoku(self, filename):
        """
        Print Sudoku solution to file with the same format
        """
        with open(filename, 'a') as f:
            for i in range(self.row):
                for j in range(self.col):
                    if len(self.domains[var]) == 1:
                        f.write('%d ' % self.domains[var][0])
                    else:
                        f.write('- ')
                f.write('\n')

    def display_puzzle(self):
        """
        Display puzzle on screen (standard output)
        """
        for i in range(self.row):
            for j in range(self.col):
                var = self.col*i + j
                if len(self.domains[var]) == 1:
                    print ('%d ' % self.domains[var][0], end='')
                else:
                    print ('- ', end='')
            print ()

    def display_result(self):
        """
        Display solution to this puzzle on screen (standard output)
        """
        for i in range(self.row):
            for j in range(self.col):
                var = self.col*i + j
                print ('%d ' % self.curr_domains[var][0], end='')
            print ()

    def sudoku_constraints(self, A, a, B, b):
        """
        r and l are row and column of a variable in a sudoku world
        b is coordinates of the box in which a variable lies
        """
        rA, lA = divmod(A, self.col)
        rB, lB = divmod(B, self.col)
        bA = (rA//3, lA//3)
        bB = (rB//3, lB//3)
        
        # Return true if a is not equal to b while they're at the same row, col or box
        if rA == rB or lA == lB or bA == bB:
            return a != b
        return True


def Sudoku_solver(sudoku, inference=no_inference):
    """
    Solve an instance of Sudoku
    AC3 is used as a preprocessing in order to maintain consistency of curr_domains
    """
    # Initialize assignment
    assignment = {}
    for var in sudoku.variables:
        if len(sudoku.domains[var]) == 1:
            assignment[var] = sudoku.domains[var][0]
    AC3(sudoku)

    backtracking_search(sudoku, assignment,
                        select_unassigned_variable=mrv,
                        order_domain_values=lcv,
                        inference=inference)


def evaluate_sudoku(filename):
    
    sudoku = Sudoku()
    sudoku.read_sudoku(filename)
    assignment = {}
    for var in sudoku.variables:
        if len(sudoku.domains[var]) == 1:
            assignment[var] = sudoku.domains[var][0]
    AC3(sudoku)
    
#    guess_level1 = evaluate_level1(sudoku, assignment)
#    print(guess_level1)

    print("Evaluating with single inference")
    guess_level1 = evaluate_levels(sudoku, assignment, 1)
    print("Double inference")
    guess_level2 = evaluate_levels(sudoku, assignment, 2)
    print("Triple Inference")
    guess_level3 = evaluate_levels(sudoku, assignment, 3)
    scores = [guess_level1, guess_level2, guess_level3]
    return scores

def calculate_difficulty(scores):
    means = [121704.33333333333, 146.66666666666666, 7.0]
    smax = [249539, 188, 5]
    smin = [0, 0, 0]

    diff = 0.0
    for i in range(3):
        diff += (scores[i] - smin[i]) / (smax[i] - smin[i])
    
    return diff/3
    





def evaluate_levels(sudoku, assignment, level = 1):
    infer_funcs = [locked_candidates, naked_subsets, hidden_single]
    combs = list(itertools.combinations(infer_funcs, level))
    
   
    guess = 0
    for t in combs:
        l = list(t)
        copy_assignment = copy.deepcopy(assignment)
        copy_sudoku = copy.deepcopy(sudoku)
#        print(guess)
        guess += backtracking_search_guess(copy_sudoku,
                                           copy_assignment,
                                           #select_unassigned_variable = mrv,
                                           order_domain_values = lcv,
                                           inference = waterfall_levels,
                                           inferlist = l
        )
    return guess


def benchmark():
    file_num = [1,2,10,15,25,26,48,51,62,76,81,82,90,95,99,100]
    score_vector = []
    for num in file_num:
        strg = str(num)
        if len(strg) == 1:
            filename = "puzzle00"+strg+".txt"
        elif len(strg) == 2:
            filename = "puzzle0"+strg+".txt"
        else:
            filename = "puzzle"+strg+".txt"
            
        scores = evaluate_sudoku(filename)
        score_vector.append(scores)


    means = []
    maximums = []
    minimums = []
    for i in range(3):
        mean_sum = 0.0
        maxi = 0.0
        mini = 1000000
        for j in range(len(score_vector)):
            mean_sum += score_vector[j][i]
            if score_vector[j][i] > maxi:
                maxi = score_vector[j][i]
            if score_vector[j][i] < mini:
                mini = score_vector[j][i]
        means.append(mean_sum / 3)
        maximums.append(maxi)
        minimums.append(mini)

    print(means)
    print(maximums)
    print(minimums)

    

    # sm = statistics.mean(scores)
    # smax = max(scores)
    # smin = min(scores)
    # span = smax - smin
    # dem = statistics.pstdev(scores)
    # with open("stastic", "a") as f:
    #     f.write("mean: %f\nmax: %f\nmin: %f\ndevia: %f" % (sm, smax, smin, dem))

    
    
    

    
        
        
def create_sudoku_from_file(filename):
    if os.path.isfile(filename):
        sudoku = Sudoku()
        sudoku.read_sudoku(filename)
        return sudoku
    

"""
Modify the file name to choose whatever puzzle you want to solve
"""

import sys
import os.path

#benchmark()
if len(sys.argv) == 2:
    num = sys.argv[1]
    num = num.strip()

    if os.path.isfile(num):
        sudoku = Sudoku()
        sudoku.read_sudoku(filename)
        sudoku.display_puzzle()
        Sudoku_solver(sudoku, waterfall)
        print()
        print('Solution:')
        print()
        sudoku.display_result()
    else:
        if len(num) == 1:
            filename = "puzzle00"+num+".txt"
        elif len(num) == 2:
            filename = "puzzle0"+num+".txt"
        else:
            filename = "puzzle"+num+".txt"
            
        if os.path.isfile(filename):
            sudoku = Sudoku()
            sudoku.read_sudoku(filename)
            sudoku.display_puzzle()
            Sudoku_solver(sudoku, waterfall)
            print()
            print('Solution:')
            print()
            sudoku.display_result()
        else:
            print("File doesn't exist! Try another one.")
            
elif len(sys.argv) == 3:
    # python3 sudoku.py -d puzzle100.txt
    cmd = sys.argv[1]
    if cmd == "-d":
        name = sys.argv[2]
        name = name.strip()
        if os.path.isfile(name):
            print("Evaluating Difficulty  (Range from very easy:0  to evil: 1) of puzzle: (this could take a minute)")
            score = evaluate_sudoku(name)
            diff = calculate_difficulty(score)
            print("Difficulty: [[[[%.4f]]]]" % diff)
        else:
            if len(name) == 1:
                filename = "puzzle00"+name+".txt"
            elif len(name) == 2:
                filename = "puzzle0"+name+".txt"
            else:
                filename = "puzzle"+name+".txt"
            
            if os.path.isfile(filename):
                print("Evaluating Difficulty  (Range from very easy:0  to evil: 1) of puzzle: (this could take a minute)")
                score = evaluate_sudoku(filename)
                diff = calculate_difficulty(score)
                print("Difficulty: [[[[%.4f]]]]" % diff)
    else:
        print("Unrecognized command: try \npython3 sudoku.py -d [filename]\n")
            
