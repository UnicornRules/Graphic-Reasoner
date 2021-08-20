# -*- coding: utf-8 -*-
"""
Created on Fri May 28 08:21:15 2021

@author: ZBook
"""

from tqdm import tqdm
import numpy as np
import json
from random import sample, randint
from copy import deepcopy
from itertools import product
import os
from time import time
import multiprocessing
from multiprocessing import Process, Manager
from multiprocessing.managers import BaseManager, NamespaceProxy
import os
import copy
import gc

def split(axiom, type='concepts'):
    axiom_s = axiom.split('<')
    if type == 'concepts':
        a1 = axiom_s[1]
        return a1.split('>', 1)[0], [a.split('>', 1)[0] for a in axiom_s[2:]]
        #return [a.split('>', 1)[0] for a in axiom_s[1:]]
    else:
        a1 = axiom_s[-1]
        return [a.split('>', 1)[0] for a in axiom_s[1:-1]], a1.split('>', 1)[0]


class saturate_process_pools:
    def __init__(self):
        # (H, A), (H,r,K), H,K is sorted tuple
        self.H2A = {}
        self.H2rK, self.K2rH = {}, {}  # here self.K2rH is just a copy of self.H2rK which accelerate the searching progress.

    def add(self, axiom):
        # axioms of form "(implies (some r B) A)" is ignored
        first_item, rest = split(axiom)
        first = (first_item,)
        axiom_s = axiom.split('(')
        if len(axiom_s) == 2:
            assert len(rest) == 1
            clause = ('H2A', first, rest[0])
            self.add_clause(clause)
            result = [clause]
            return result

        result = []
        literal = axiom.split('(')[2]

        if literal[0] == 's':
            assert len(rest) == 2
            r, K = rest[0], (rest[1],)
            clause = ('H2rK', first, r, K)
            self.add_clause(clause)
            result.append(clause)

        elif literal[1] == 'n':
            for rest_term in rest:
                clause = ('H2A', first, rest_term)
                self.add_clause(clause)
                result.append(clause)

            if axiom[1] == 'e':
                rest_tuple = tuple(sorted(rest))
                clause = ('H2A', rest_tuple, first)
                self.add_clause(clause)
                result.append(clause)
        return result

    # add clause, return True if it is new clause, False if not. if type !='add', only return True, False, do not add.
    def add_clause(self, clause, type='add'):
        if clause[0] == 'H2A':
            H, A = clause[1], clause[2]
            # add (H,A)
            if H in self.H2A and A not in self.H2A[H]:
                if type == 'add':
                    self.H2A[H].add(A)
                return True
            elif H not in self.H2A:
                if type == 'add':
                    self.H2A[H] = {A}
                return True
            return False

        elif clause[0] == 'H2rK':
            H, r, K = clause[1], clause[2], clause[3]
            f = False
            # add (H,r,K)
            if K in self.K2rH:
                if r in self.K2rH[K] and H not in self.K2rH[K][r]:
                    if type == 'add':
                        self.K2rH[K][r].add(H)
                    f = True
                elif r not in self.K2rH[K]:
                    if type == 'add':
                        self.K2rH[K][r] = {H}
                    f = True
            else:
                if type == 'add':
                    self.K2rH[K] = {r: {H}}
                f = True

            if H in self.H2rK:
                if r in self.H2rK[H] and K not in self.H2rK[H][r]:
                    if type == 'add':
                        self.H2rK[H][r].add(K)
                    f = True
                elif r not in self.H2rK[H]:
                    if type == 'add':
                        self.H2rK[H][r] = {K}
                    f = True
            else:
                if type == 'add':
                    self.H2rK[H] = {r: {K}}
                f = True
            return f

    def not_vaid(self):
        if not self.K2rH or not self.H2A:
            return True
        else:
            return False


class saturate_ini_pools:
    def __init__(self):
        # A\sqsubseteq \exists r.B or  \exists r.B \sqsubseteq A
        self.A2rB, self.B2rA = {}, {}

        #  A\sqsubseteq B, A_1\cap....\cap A_n\sqsubseteq B, A tov {...,A_i,...}
        self.A2B, self.Ai2B, self.A2Ai = {}, {}, {}

        # A to (r, B), A\sqsubseteq \forall r.B
        #self.A2rB_universal = {}
 #unnecessary
        # r1\circ...\circ rn \sqsubseteq r
        self.ri2r, self.r2ri = {}, {}

    def add(self, axiom):
        first, rest = split(axiom)
        axiom_s = axiom.split('(')
        # (implies/equi A B)
        if len(axiom_s) == 2:
            assert len(rest) == 1
            clause = ('A2B', first, rest[0])
            self.add_clause(clause)
            result = [clause]
            return result

        result = []
        literal = axiom.split('(')[2]
        if literal[0] == 's':  # (... (some...))
            assert len(rest) == 2
            if axiom.split(' ')[1][0] == '(':
                #(impies (some...) ...)
                clause = ('B2rA',  rest[0], first, rest[1],)
            else:
                #(impies ... (some...)) or (equivalence ... (some...))
                if axiom[1] == 'e':
                    assert axiom.split(' ')[1][1] != '('
                    clause = ('B2rA', rest[1], rest[0], first)
                    self.add_clause(clause)
                    result.append(clause)

                clause = ('A2rB', first, rest[0], rest[1])
            self.add_clause(clause)
            result.append(clause)

       # elif literal[1] == 'l':  # (... (all...))
        #    clause = ('A2rB_universal', first, rest[0], rest[1])
         #   self.add_clause(clause)
         #   result.append(clause)
            #print(axiom)
            #assert axiom[1] != 'e' # it is impossible it has form (implies... (all...))

        else:  # (... (and...))
            for rest_term in rest:
                #print(rest_term)
                clause = ('A2B', first, rest_term)
                self.add_clause(clause)
                result.append(clause)
            #print('aaaa')
            #print(axiom)"""
            if axiom[1] == 'i':
                union=[first]
                union+=rest[:-1]
                conc = rest[-1]
                union=tuple(union)
                #print(union)
                #print(conc)
                clause = ('Ai2B', union , conc)
                self.add_clause(clause)
                result.append(clause)
                if conc in self.A2Ai:
                    self.A2Ai[conc].add(union)
                else:
                    self.A2Ai[conc] = {union}
            if axiom[1] == 'e':
                rest_tuple = tuple(sorted(rest))
                clause = ('Ai2B', rest_tuple , first)
                self.add_clause(clause)
                result.append(clause)
                for A in rest_tuple:
                    if A in self.A2Ai:
                        self.A2Ai[A].add(rest_tuple)
                    else:
                        self.A2Ai[A] = {rest_tuple}

        return result

    def add_role_axioms(self, axiom):
        begin, last = split(axiom, 'role')
        begin = tuple(begin)
        if begin in self.ri2r:
            self.ri2r[begin].add(last)
        else:
            self.ri2r[begin] = {last}

        if len(begin) > 1:
            for role in begin:
                if role in self.r2ri:
                    self.r2ri[role].add(begin)
                else:
                    self.r2ri[role] = {begin}

        result = ('ri2r', begin, last)
        return result

    # add clause, return True if it is new clause, False if not. if type !='add', only return True, False, do not add.
    def add_clause(self, clause, type='add'):
        if clause[0] == 'A2rB':
            # (implies A (r,B))
            A, r, B = clause[1], clause[2], clause[3]
            if A in self.A2rB:
                if r in self.A2rB[A] and B not in self.A2rB[A][r]:
                    if type == 'add':
                        self.A2rB[A][r].add(B)
                    return True
                elif r not in self.A2rB[A]:
                    if type == 'add':
                        self.A2rB[A][r] = {B}
                    return True
            else:
                if type == 'add':
                    self.A2rB[A] = {r: {B}}
                return True
            return False

        elif clause[0] == 'B2rA':
            # add (implies (some r B), A)
            B, r, A = clause[1], clause[2], clause[3]
            if B in self.B2rA:
                if r in self.B2rA[B] and A not in self.B2rA[B][r]:
                    if type == 'add':
                        self.B2rA[B][r].add(A)
                    return True
                elif r not in self.B2rA[B]:
                    if type == 'add':
                        self.B2rA[B][r] = {A}
                    return True
            else:
                if type == 'add':
                    self.B2rA[B] = {r: {A}}
                return True
            return False

        elif clause[0] == 'A2B':
            A, B = clause[1], clause[2]
            # check if h \sqsubseteq A1 have appeared
            if A in self.A2B and B not in self.A2B[A]:
                if type == 'add':
                    self.A2B[A].add(B)
                return True
            elif A not in self.A2B:
                if type == 'add':
                    self.A2B[A] = {B}
                return True
            return False

        elif clause[0] == 'A2rB_universal':
            A, r, B = clause[1], clause[2], clause[3]
            # add (H,r,K)
            if A in self.A2rB_universal:
                if r in self.A2rB_universal[A] and B not in self.A2rB_universal[A][r]:
                    if type == 'add':
                        self.A2rB_universal[A][r].add(B)
                    return True
                elif r not in self.A2rB_universal[A]:
                    if type == 'add':
                        self.A2rB_universal[A][r] = {B}
                    return True
            else:
                if type == 'add':
                    self.A2rB_universal[A] = {r: {B}}
                return True
            return False

        elif clause[0] == 'Ai2B':
            Ai, A = clause[1], clause[2]
            if Ai in self.Ai2B and A not in self.Ai2B[Ai]:
                if type == 'add':
                    self.Ai2B[Ai].add(A)
                    for A in Ai:
                        if A in self.A2Ai:
                            self.A2Ai[A].add(Ai)
                        else:
                            self.A2Ai[A] = {Ai}

                return True
            elif Ai not in self.Ai2B:
                #print(clause)
                if type == 'add':
                    self.Ai2B[Ai] = {A}
                    for A in Ai:
                        if A in self.A2Ai:
                            self.A2Ai[A].add(Ai)
                        else:
                            self.A2Ai[A] = {Ai}
                return True
            return False


class saturate_pools:
    def __init__(self):
        # (H, A), (H,r,K)
        self.H2A, self.H2rK = {}, {}

    def add(self, axiom):
        first_item, rest = split(axiom)
        first = (first_item,)
        axiom_s = axiom.split('(')
        if len(axiom_s) == 2:
            #print(axiom)
            assert len(rest) == 1
            if first in self.H2A:
                self.H2A[first].update(rest)
            else:
                self.H2A[first] = set(rest)

            result = [('H2A', first, rest[0])]
            return result

        result = []
        literal = axiom.split('(')[2]

        if literal[0] == 's':
            #print(rest, axiom)
            assert len(rest) == 2
            r, K = rest[0], (rest[1],)
            if first in self.H2rK:
                if r in self.H2rK[first]:
                    self.H2rK[first][r].add(K)
                else:
                    self.H2rK[first][r] = {K}
            else:
                self.H2rK[first] = {r: {K}}
            result.append(('H2rK', first, r, K))

        elif literal[1] == 'n':
            if first in self.H2A:
                self.H2A[first].update(rest)
            else:
                self.H2A[first] = set(rest)

            result += [('H2A', first, rest_term) for rest_term in rest]

            if axiom[1] == 'e':
                rest_tuple = tuple(sorted(rest))
                if rest_tuple in self.H2A:
                    self.H2A[rest_tuple].add(first)
                else:
                    self.H2A[rest_tuple] = {first}
                result.append(('H2A', rest_tuple, first))

        return result

    # add clause, return True if it is new clause, False if not. if type !='add', only return True, False, do not add.
    def add_clause(self, clause, type='add'):
        if clause[0] == 'H2A':
            H, A = clause[1], clause[2]
            # add (H,A)
            if H in self.H2A and A not in self.H2A[H]:
                if type == 'add':
                    self.H2A[H].add(A)
                return True
            elif H not in self.H2A:
                if type == 'add':
                    self.H2A[H] = {A}
                return True
            return False

        elif clause[0] == 'H2rK':
            H, r, K = clause[1], clause[2], clause[3]
            # add (H,r,K)
            if H in self.H2rK:
                if r in self.H2rK[H] and K not in self.H2rK[H][r]:
                    if type == 'add':
                        self.H2rK[H][r].add(K)
                    return True
                elif r not in self.H2rK[H]:
                    if type == 'add':
                        self.H2rK[H][r] = {K}
                    return True
            else:
                if type == 'add':
                    self.H2rK[H] = {r: {K}}
                return True
            return False

    def not_vaid(self):
        if not self.H2A or not self.H2rK:
            return True
        else:
            return False


def tensor_prod(l1, l2):   #takes 2 lists of sets 
    result = []
    if not l1:              #if l1 empty/l2 empty, return the non-empty one
        return l2
    if not l2:
        return l1
    len1, len2 = len(l1), len(l2)
    for i in range(len1):                   
        for j in range(len2):                           
            combined_path = l1[i].union(l2[j])          #union des sets l1[i] et l2[1]
            result.append(combined_path)                #append the union in results
    return result                                       #return the list of all unions


def filter(S_in):  
    l = len(S_in)
    if l < 2:
        return S_in
    S = sorted(S_in, key=lambda i: len(i), reverse=False) #sort by length of element
    result = []
    for s in S:  #for each element
        if not s:
            continue

        flag_1 = False     #initialize a boolean to false
        for e in result:
            if len(e) > len(s):
                continue
            if e.issubset(s):   #if all e element are in s (can't be the case if len(e)>len(s))
                flag_1 = True
                break
        if flag_1:              #If flag 1 is not true : we add s in results
            continue
        else:
            result.append(s)
    return result


def add_e(l1, e):  #add e to every set of l1 (lists of set) and return the modified copy
    assert l1
    result = []
    for l in l1:
        l_new = copy.deepcopy(l)
        l_new.add(e)
        result.append(l_new)
    return result


def delete_c(l, c):  #delet a set from l 
    result = []
    for s in l:
        if c in s:
            continue
        else:
            result.append(s)
    return result


def unfold(dic, type=None, out=None):
    result_dic = {}
    current_key = set([])
    calculated_key = set([])
    flag_loop = False

    def unfold_A(k):
        nonlocal result_dic, current_key, flag_loop, calculated_key, dic
        if k in result_dic:            #if k already in result dic, we just ask for the key of result_dic(k)
            return set(result_dic[k])
        else:
            current_key.add(k)
            calculated_key.add(k)
            if type:
                result = set([])
            else:
                result = set(dic[k])
            for n in dic[k]:
                if n == k:
                    continue
                # print(n)
                if n in current_key:
                    flag_loop = True
                    # print(current_key)
                    continue
                if n in calculated_key:
                    if n in result_dic:
                        result.update(result_dic[n])
                    continue
                elif n not in dic:
                    result.add(n)
                else:
                    result.update(unfold_A(n))
            current_key.remove(k)
            if not current_key:
                flag_loop = False
                calculated_key = set([])
            if not flag_loop:
                if out:
                    result_dic[k] = list(result)
                else:
                    result_dic[k] = result
            # return list(result)
            return result

    for k in dic:
        assert current_key == set([])
        assert calculated_key == set([])
        assert flag_loop == False
        unfold_A(k)
    return result_dic


# count how many times '(some' and '(and' appears in one axiom
def depth_bigger_than(one_axiom, k):
    axiom_split = one_axiom.split('(')
    i = 0
    for s in axiom_split:
        if s:
            if s[0] == 'a' or s[0] == 's':
                i += 1
            if i >= k:
                return True
    return False


def trans_back(axioms):
    return axioms.replace('(implies ', 'SubClassOf(').replace('(equivalent ', 'EquivalentClasses(').replace('(some ',
                                                                                                            'ObjectSomeValuesFrom(').replace(
        '(and ', 'ObjectIntersectionOf(')


def formal_form(a):
    '''
    :param a: "some r A" or "and A B C..." or "SubObjectPropertyOf(...r1, r2...)"
    :return: "some r A" or "ABC..." %sorted% or (..r1,r2,...) %same order as above%
    '''
    # print(a)
    if a[0] == 's':
        return a
    elif a[0] == 'a':
        a_s = ''.join(sorted(a.split(' ')[1:]))
        return a_s
    else:
        assert a[0] == 'S'
        result = '\t'.join([a_s.split('>')[0] for a_s in a.split('<')[1:]])
        return result


def mkdir(path):
    folder = os.path.exists(path)
    if not folder:
        os.makedirs(path)


def update_equi(l, a, b):
    for s in l:
        if {a, b} & s:
            s.update({a, b})
        else:
            l.append({a, b})
    return l

def cut_axiom(one_axiom):
    '''
    :param one_axiom: str ... str (...(...))(...) str(...)
    :return: [str,'',str,'','',str,'',], [...,(...(...)),(...),(...)]
    '''
    l, i = len(one_axiom), 0
    result_str, result, type_1 = '', [], 'outside'
    while i < l:
        if type_1 == 'outside':
            if one_axiom[i] == '(':
                type_1 = 'inside'
                i += 1
            else:
                result_str += one_axiom[i]
                i += 1
        else:
            count, count_term_1, start_id = 0, 1, i
            while i < l:
                if one_axiom[i] == '(':
                    count_term_1 += 1
                elif one_axiom[i] == ')':
                    count_term_1 -= 1
                    if count_term_1 == 0:
                        result.append(one_axiom[start_id:i])
                        result_str += '*'
                        i += 1
                        type_1 = 'outside'
                        break
                i += 1
    return result_str.split('*'), result


def renew_tuple(K, B):
    if B in K:
        return K
    else:
        K_new = list(K)
        K_new.append(B)
        return tuple(sorted(K_new))


def clause2axiom(clause):
    result = '(implies '
    if clause[0] == 'H2rK':
        if len(clause[1]) == 1:
            result += clause[1][0] + ' '
        else:
            result += f'(and {",".join(clause[1])}) '

        result += f'(some {clause[2]} '

        if len(clause[3]) == 1:
            result += clause[3][0] + '))'
        else:
            result += f'(and {",".join(clause[1])})))'
        return result

    elif clause[0] == 'H2A':
        if len(clause[1]) == 1:
            result += clause[1][0] + ' '
        else:
            result += f'(and {",".join(clause[1])}) '

        result += clause[2] + ')'
        return result
    else:
        return False


class Ontology:
    def __init__(self, name_ontology, normalized=False):
        self.axioms, self.axioms_RI, self.axioms_RC, self.concepts, self.relations = {}, {}, {}, set([]), set([])
        # RI for role inclusion, RC for role chain
        self.axioms_normalized, self.mapback, self.normalize_dic = {}, {}, {}

        self.num_axiom_normalized, self.new_normalize_concepts, self.current_axiom = 0, 0, 0
        self.num_axiom, self.num_no_el_axiom = 0, 0

        self.valid_first_literals = {'E', 'S', 'T'}  # Equivalence() or Sub...() or Transverse
        self.filter_box = ['ObjectUnionOf', 'ObjectComplementOf', 'ObjectOneOf',
                           'ObjectHasValue', 'ObjectHasSelf', 'ObjectMinCardinality', 'ObjectMaxCardinality',
                           'ObjectExactCardinality', 'DataSomeValuesFrom', 'DataAllValuesFrom', 'DataHasValue',
                           'DataMinCardinality', 'DataMaxCardinality', 'DataExactCardinality',
                           'ClassAxiom', 'ObjectPropertyAxiom', 'DataPropertyAxiom', 'DatatypeDefinition', 'HasKey',
                           'Assertion',
                           'Annotation', 'Datatype', 'DataIntersectionOf', 'DataUnionOf', 'DataComplementOf',
                           'DataOneOf',
                           'DatatypeRestriction', 'DisjointClasses', 'DisjointUnion',
                           'DisjointObjectProperties',
                           'InverseObjectProperties', 'ObjectPropertyDomain', 'FunctionalObjectProperty',
                           'InverseFunctionalObjectProperty', 'ReflexiveObjectProperty', 'IrreflexiveObjectProperty',
                           'SymmetricObjectProperty', 'AsymmetricObjectProperty', 'SubDataPropertyOf',
                           'EquivalentDataProperties', 'DisjointDataProperties', 'DataPropertyDomain',
                           'DataPropertyRange', 'FunctionalDataProperty', 'SameIndividual', 'DifferentIndividuals',
                           'ObjectPropertyAssertion', 'NegativeObjectPropertyAssertion', 'DataPropertyAssertion',
                           'NegativeDataPropertyAssertion']  # 'TransitiveObjectProperty','ObjectAllValuesFrom','ObjectPropertyRange','Declaration','EquivalentObjectProperties',  'ClassAssertion',

        print('loading ontology:')
        with open(f'workspace/{name_ontology}/{name_ontology}.owl', 'r') as f:
            with open(f'Ontologies-Less-Than-10000/{name_ontology}.owl', 'r') as f:
                data = f.readlines()
                for line in tqdm(data):
                    self.renew(line)
        if not normalized:
            self.normalize()
        print('num_el_axioms, non_el_axioms:', self.num_axiom, self.num_no_el_axiom)
        self.save(name_ontology)

    def save(self, name_ontology):
        # path = f'workspace/{name_ontology}/data/'
        path = f'result-Ontologies-Less-Than-10000/{name_ontology}/data/'
        mkdir(path)
        jsobj1 = json.dumps(self.axioms_RI)
        fileObject1 = open(f'{path}role_inclusion.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.axioms_RC)
        fileObject1 = open(f'{path}role_chain.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.axioms)
        fileObject1 = open(f'{path}axioms.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.axioms_normalized)
        fileObject1 = open(f'{path}axioms_normalized.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.mapback)
        fileObject1 = open(f'{path}mapback.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()
        return

    def renew(self, line):
        if '(' not in line or '<' not in line or 'Assertion(' in line:
            return
        if line[:19] == 'ObjectPropertyRange':
            axiom_new = 'SubClassof( <owl:Thing> ObjectAllValuesFrom(' + line[20:] + ')'
            # print(line, axiom_new)
            self.axioms[axiom_new] = self.num_axiom
            self.num_axiom += 1
            return

        for a in self.filter_box:
            if a in line:
                # print(line)
                self.num_no_el_axiom += 1
                return

        if line[0] == 'D':  # Declaration()
            if line[11:13] == '(C':  # Class
                self.concepts.add(line.split('<', 1)[1][:-3])
            elif line[11:13] == '(O':  # Object
                self.relations.add(line.split('<', 1)[1][:-3])

        elif line[0] in self.valid_first_literals:

            # !!!!!!!!to do: transform axiom (implies (all r B) A) using negation

            if 'Propert' in line:  # to include two cases "Property" or "Properties"
                if 'Chain' in line:
                    assert line[0] != 'E'
                    self.axioms_RC[line[:-1]] = self.num_axiom
                else:
                    if line[:16] == 'TransitiveObject':
                        role_name = line.split('<', 1)[1].split('>', 1)[0]
                        trans_axiom = f'SubObjectPropertyOf(ObjectPropertyChain(<{role_name}> <{role_name}>) <{role_name}>)'
                        self.axioms_RC[trans_axiom] = self.num_axiom
                    elif line[:26] == 'EquivalentObjectProperties':
                        r_list = [a.split('>')[0] for a in line.split('<')[1:]]
                        axiom_1 = f'SubObjectPropertyOf<{r_list[0]}> <{r_list[1]}>)'
                        axiom_2 = f'SubObjectPropertyOf(<{r_list[1]}> <{r_list[0]}>)'
                        # print(axiom_1, axiom_2)
                        self.axioms_RI[axiom_1] = self.num_axiom
                        self.axioms_RI[axiom_2] = self.num_axiom
                    else:
                        self.axioms_RI[line[:-1]] = self.num_axiom
            else:
                line_other_form = line.replace('SubClassOf(', '(implies ').replace('EquivalentClasses(',
                                                                                   '(equivalent ').replace(
                    'ObjectSomeValuesFrom(', '(some ').replace('ObjectIntersectionOf(', '(and ').replace(
                    'ObjectAllValuesFrom(', '(all').replace('owl:Thing', '<owl:Thing>').replace('owl:Nothing',
                                                                                              '<owl:Nothing>')
                self.axioms[line_other_form[:-1]] = self.num_axiom
            self.num_axiom += 1

    # find all the existing definition (equivalence ... ) avoid to add this defi again when normalize the ontology.
    def preprocess(self):
        for axiom in self.axioms:
            if axiom[1] == 'e':
                # not depth_bigger_than(one_axiom, 2) means the axioms contain at most one "some" or "and"
                if len(axiom.split('(')) > 2 and not depth_bigger_than(axiom, 2):
                    # get the item **** inside (equivalent\implies <#...> (****) )
                    def_terms = formal_form(axiom.split('(')[-1].split(')')[0])
                    defined_term = axiom.split(' ')[1]
                    if def_terms not in self.normalize_dic.keys():
                        self.mapback[def_terms] = self.axioms[axiom]
                        self.normalize_dic[def_terms] = defined_term

    def normalize_one_term_begin(self, axiom):
        if depth_bigger_than(axiom, 2):
            # get the item **** inside (equi\implies <#...> (****) )
            axiom_str_rest, axiom_cutted = cut_axiom(axiom[1:-1])
            result = axiom_str_rest[0]
            assert len(axiom_cutted) <= 2
            for i, one_axiom_cutted in enumerate(axiom_cutted):
                if len(result.split('<')) >= 2:
                    k = 2
                    result += '('
                else:
                    k = 1
                while depth_bigger_than(one_axiom_cutted, k):
                    one_axiom_cutted = self.normalize_one_term_middle(one_axiom_cutted)
                result += one_axiom_cutted
                if k == 2:
                    result += ')'
                result += axiom_str_rest[i + 1]
            return '(' + result + ')'
        else:
            return axiom

    def normalize_one_term_middle(self, part_axiom):
        if depth_bigger_than(part_axiom, 2):
            axiom_str_rest, axiom_cutted = cut_axiom(part_axiom)
            result = axiom_str_rest[0]
            for i, one_axiom_cutted in enumerate(axiom_cutted):
                while depth_bigger_than(one_axiom_cutted, 1):
                    one_axiom_cutted = self.normalize_one_term_middle(one_axiom_cutted)
                result += one_axiom_cutted
                result += axiom_str_rest[i + 1]
            return result
        else:
            one_axiom_form = formal_form(part_axiom)
            if one_axiom_form not in self.normalize_dic.keys():
                new_normalized_concept = f'<#N{self.new_normalize_concepts}>'
                self.new_normalize_concepts += 1
                self.concepts.add(new_normalized_concept)
                self.normalize_dic[one_axiom_form] = new_normalized_concept

                self.axioms_normalized[
                    f'(equivalent {new_normalized_concept} ({part_axiom}))'] = self.num_axiom_normalized
                self.num_axiom_normalized += 1

            return self.normalize_dic[one_axiom_form]

    def normalize(self):
        # self.preprocess()
        for axiom in self.axioms:
            self.axioms_normalized[self.normalize_one_term_begin(axiom)] = self.num_axiom_normalized
            self.mapback[self.num_axiom_normalized] = self.axioms[axiom]
            self.num_axiom_normalized += 1
        print(
            f'length of ontology, normalization ontology(exclude role chain or role inclusion): {len(self.axioms)}, {self.num_axiom_normalized}')

    def len(self):
        return len(self.axioms_normalized) + len(self.axioms_RC) + len(self.axioms_RI)
    
class saturate:
    def __init__(self, name_ontology, normalized=False):
        self.ontology = Ontology(name_ontology, normalized)

        self.initial_pool = saturate_pools()
        self.ontology_pool = saturate_ini_pools()
        self.processed_pool = saturate_process_pools()

        # self.ind = self.ontology.len()
        self.ind = 0
        self.ontology_len = self.ontology.len()
        self.clause2ind = {}
        # self.id_axioms2ind = {}
        self.saturate_progress, self.num_saturated = {}, 0
        # self.savepath = f'workspace/{name_ontology}/data/'
        self.savepath = f'result-Ontologies-Less-Than-10000/{name_ontology}/data/'
        self.initial()
        self.owlThing2rB = {}

    def initial(self):
        for axiom in self.ontology.axioms_normalized:
            clauses = self.initial_pool.add(axiom)
            for clause in clauses:
                self.add_new_clause(clause, type='fix')  #type = fix allows not to increment the ind

            clauses1 = self.ontology_pool.add(axiom)
            for clause in clauses1:
                self.add_new_clause(clause, type='fix')
            self.clause2ind[('original', axiom)] = self.ind
            self.ind += 1

        for axiom in self.ontology.axioms_RC:
            clause = self.ontology_pool.add_role_axioms(axiom)
            self.clause2ind[clause] = self.ind
            self.clause2ind[('original', axiom)] = self.ind
            self.ind += 1

        for axiom in self.ontology.axioms_RI:
            clause = self.ontology_pool.add_role_axioms(axiom)
            self.clause2ind[clause] = self.ind
            self.clause2ind[('original', axiom)] = self.ind
            self.ind += 1

        self.owlThing2rB = self.ontology_pool.B2rA.get('owl:Thing')

    def record_saturate_process(self, pre, con):
        pre = list(pre)
        if con in self.saturate_progress:
            self.saturate_progress[con].append(pre)
        else:
            self.saturate_progress[con] = [pre]
        self.num_saturated += 1

    def one_turn_H2A(self):
        if not self.initial_pool.H2A:
            return False
        H = sample(self.initial_pool.H2A.keys(), 1)[0]
        A = self.initial_pool.H2A[H].pop()
        if not self.initial_pool.H2A[H]:
            del self.initial_pool.H2A[H]
        ind_HA = self.clause2ind[('H2A', H, A)]

        # (H, A)   (A,B) --> (H, B).
        B_list = self.ontology_pool.A2B.get(A)
        if B_list:
            for B in B_list: 
                clause = ('H2A', H, B)
                self.add_new_clause(clause)
                pre = {ind_HA, self.clause2ind[('A2B', A, B)]}
                self.record_saturate_process(pre, self.clause2ind[clause])

        # (H, A),(H, A1),...,(H,An)    ({A,...Ai...},{B}) --> (H, B). (H, Ai) in processed_pool
        Ai_set_list = self.ontology_pool.A2Ai.get(A)
        Ai_avaliable = deepcopy(self.processed_pool.H2A.get(H))
        if Ai_set_list and Ai_avaliable:
            Ai_avaliable.update(H)  # in case (A1, A1),...,(A1,An)    ({...Ai...},{B})  to (A1, B)  "update(H)"??
            for Ai_set in Ai_set_list:
                for Ai in Ai_set:
                    if Ai != A and Ai not in Ai_avaliable:
                        break
                else:
                    for B in self.ontology_pool.Ai2B[Ai_set]:
                        clause = ('H2A', H, B)
                        self.add_new_clause(clause)
                        pre = {self.clause2ind[('H2A', H, Ai_new)] for Ai_new in Ai_set if
                               Ai_new != A and Ai_new not in H}
                        pre.add(self.clause2ind[('Ai2B', Ai_set, B)])
                        self.record_saturate_process(pre, self.clause2ind[clause])

        # (H, A)    (A, rB) --> (H, r, B)
        rB_dic = self.ontology_pool.A2rB.get(A)
        if rB_dic:
            for r in rB_dic:
                for B in rB_dic[r]:
                    clause = ('H2rK', H, r, (B,))
                    self.add_new_clause(clause)
                    pre = {self.clause2ind[('A2rB', A, r, B)], ind_HA}
                    self.record_saturate_process(pre, self.clause2ind[clause])

        # (H1, r, H), (H, A)    (rA, B) --> (H1, B)
        r2H1_dic = self.processed_pool.K2rH.get(H)
        r2A_dic = self.ontology_pool.B2rA.get(A)
        if r2H1_dic and r2A_dic:
            for r in r2H1_dic.keys() & r2A_dic.keys():
                for H1, B in product(r2H1_dic[r], r2A_dic[r]):
                    clause = ('H2A', H1, B)
                    self.add_new_clause(clause)
                    pre = {ind_HA, self.clause2ind[('H2rK', H1, r, H)], self.clause2ind[('B2rA', A, r, B)]}
                    self.record_saturate_process(pre, self.clause2ind[clause])

        clause = ('H2A', H, A)
        self.processed_pool.add_clause(clause)
        return True

    def one_turn_H2rK(self):
        # {H:{r:[K1,..,K_n],...}, ...}
        if not self.initial_pool.H2rK:
            return False
        H = sample(self.initial_pool.H2rK.keys(), 1)[0]
        r = sample(self.initial_pool.H2rK[H].keys(), 1)[0]
        K = self.initial_pool.H2rK[H][r].pop()
        if not self.initial_pool.H2rK[H][r]:
            del self.initial_pool.H2rK[H][r]
            if not self.initial_pool.H2rK[H]:
                del self.initial_pool.H2rK[H]
        ind_HrK = self.clause2ind[('H2rK', H, r, K)]

        # (H, r, K), (K, A)    (rA, B) --> (H, B)
        A_list = self.processed_pool.H2A.get(K)
        if not A_list:
            A_list = K
        else:
            A_list.update(K)
        for A in A_list:
            r2B_dic = self.ontology_pool.B2rA.get(A)
            if r2B_dic:
                B_list = r2B_dic.get(r)
                if B_list:
                    for B in B_list:
                        clause = ('H2A', H, B)
                        self.add_new_clause(clause)
                        if A in K:
                            pre = {ind_HrK, self.clause2ind[('B2rA', A, r, B)]}
                        else:
                            pre = {ind_HrK, self.clause2ind[('H2A', K, A)], self.clause2ind[('B2rA', A, r, B)]}
                        self.record_saturate_process(pre, self.clause2ind[clause])

        # ......  +  role axioms --> conclusion
        if len(H) == 1 and len(K) == 1:
            # (A, r, B)...    r\sqsubseteq s to (A, s, B)
            r_tuple = (r,)
            s_list = self.ontology_pool.ri2r.get(r_tuple)
            if s_list:
                for s in s_list:
                    clause = ('H2rK', H, s, K)
                    self.add_new_clause(clause)
                    pre = {ind_HrK, self.clause2ind[('ri2r', r_tuple, s)]}
                    self.record_saturate_process(pre, self.clause2ind[clause])

            r_squence_list = self.ontology_pool.r2ri.get(r)
            if r_squence_list:
                for r_sequence in r_squence_list:
                    # (A_0, r, A_1), (A_1, s, A_2)   r\circ s\sqsubseteq t --> (A_0, t, A_2)
                    if r_sequence[0] == r:
                        r2K_dic = self.processed_pool.H2rK.get(K)
                        if r2K_dic and r_sequence[1] in r2K_dic:
                            A2_tuple_list = r2K_dic[r_sequence[1]]
                            for A2_tuple in A2_tuple_list:
                                for t in self.ontology_pool.ri2r[r_sequence]:
                                    clause = ('H2rK', H, t, A2_tuple)
                                    self.add_new_clause(clause)
                                    pre = {ind_HrK, self.clause2ind[('ri2r', r_sequence, t)],
                                           self.clause2ind[('H2rK', K, r_sequence[1], A2_tuple)]}
                                    self.record_saturate_process(pre, self.clause2ind[clause])
                    else:
                        # (A_0, s, A_1), (A_1, r, A_2)   s\circ r\sqsubseteq t --> (A_0, t, A_2)
                        assert r_sequence[1] == r
                        s2A0_dic = self.processed_pool.K2rH.get(H)
                        if s2A0_dic and r_sequence[0] in s2A0_dic:
                            A0_tuple_list = s2A0_dic[r_sequence[0]]
                            for A0_tuple in A0_tuple_list:
                                for t in self.ontology_pool.ri2r[r_sequence]:
                                    clause = ('H2rK', A0_tuple, t, K)
                                    self.add_new_clause(clause)
                                    pre = {ind_HrK, self.clause2ind[('ri2r', r_sequence, t)],
                                           self.clause2ind[('H2rK', A0_tuple, r_sequence[0], H)]}
                                    self.record_saturate_process(pre, self.clause2ind[clause])

        clause = ('H2rK', H, r, K)
        self.processed_pool.add_clause(clause)
        return True

    def run(self,a=0):
        while True:
            #print(len(self.initial_pool.H2A)+len(self.initial_pool.H2rK))
            if a == 0:
                f = self.one_turn_H2A()
                if not f:
                    f1 = self.one_turn_H2rK()
                    if not f1:
                        break
            else:
                f = self.one_turn_H2rK()
                if not f:
                    f1 = self.one_turn_H2A()
                    if not f1:
                        break
        self.save()
        return self
    
    def add_new_clause(self, clause, type='non-fix'):
        if clause not in self.clause2ind:
            _ = self.initial_pool.add_clause(clause)
            self.clause2ind[clause] = self.ind
            if type == 'non-fix':
                self.ind += 1

    def save(self):
        mkdir(self.savepath)
        jsobj1 = json.dumps(self.saturate_progress)
        fileObject1 = open(f'{self.savepath}saturate_progress.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        with open(f'{self.savepath}clause2ind.txt', 'w') as f:
            f.write('original ontologies(normalized):\n')
            for clause, id_clause in self.clause2ind.items():
                if clause[0] == 'original':
                    f.write(f"{id_clause}-{clause[1]}\n")
            f.write('\n####################################\n')
            for clause, id_clause in self.clause2ind.items():
                if clause[0] != 'original':
                    if id_clause >= self.ontology_len:
                        clause_axiom_form = clause2axiom(clause)
                        if clause_axiom_form:
                            f.write(f"{id_clause}-{clause_axiom_form}\n")
        return
def crea_graph_1(S):
    graph = nx.MultiDiGraph()
    for keys in S.ontology_pool.A2B:
        A =  S.ontology_pool.A2B[keys] 
      
        
  
    
    
    for keys in S.ontology_pool.B2rA:
        G = S.ontology_pool.B2rA[keys]
        print(G)
        for key in G:
            A = G[key]
            for elem in A:
                graph.add_node(elem)
                graph.add_node(keys)
                graph.add_edge(keys,elem)
                graph[keys,elem]['role_before'] = str(key)
    return(graph)   
    
    
    
def crea_graph_2(S):
    graph = nx.MultiDiGraph()
    for keys in S.ontology_pool.A2B:
        A =  S.ontology_pool.A2B[keys]                                                                                      
        graph.add_node(tuple(A)[0])
        graph.add_node(keys)
        graph.add_edge(keys,tuple(A)[0])
        
        
    for keys in S.ontology_pool.A2rB:
        G = S.ontology_pool.A2rB[keys]
        for key in G:
            A = G[key]
            graph.add_node(tuple(A)[0])
            graph.add_node({keys:key})
            graph.add_edge(keys,tuple(A)[0])
    
    
    for keys in S.ontology_pool.B2rA:
        G = S.ontology_pool.B2rA[keys]
        for key in G:
            A = G[key]
            graph.add_node(tuple(A)[0])
            graph.add_node({keys:key})
            graph.add_edge(keys,tuple(A)[0])
    return(graph)

def turn_dict_tuple(dic):
    list_edges = []
    for keys in dic :
        dic_1 = dic[keys]
        if type(dic_1)==dict:
            for key in dic_1:
                for elem in dic_1[key]:
                    list_edges.append(((keys,key),elem))
        elif type(dic_1)==set:
            for elem in dic_1:
                list_edges.append((keys,elem))
    return(list_edges)

def turn_pool_tuple(S):
    list_edges_A2B = []
    list_edges_roles = []
    for keys in S.ontology_pool.A2rB :
        dic_1 = S.ontology_pool.A2rB[keys]
        for key in dic_1:
            for elem in dic_1[key]:
                list_edges_roles.append(((keys),(key,elem)))
    for keys in S.ontology_pool.B2rA :
        dic_1 = S.ontology_pool.B2rA[keys]
        for key in dic_1:
            for elem in dic_1[key]:
                list_edges_roles.append(((keys,key),elem))
    for keys in S.ontology_pool.A2B:
        for elem in S.ontology_pool.A2B[keys]:
            list_edges_A2B.append((keys,elem))
    return(list_edges_A2B,list_edges_roles)
            



def unfold(dic, type=None, out=None):

    '''

    
    works well with A2B, not with A2rB (only with non-nested dict) need to convert
    :param dic: input dictionary

    :param type: if type is true, we do not include the initial edges in the graph

    :param out: if out is true, the we the set of nodes A is connected to is collect in a list

    :return: 

    '''

    result_dic = {}

    current_key = set([])

    calculated_key = set([])

    flag_loop = False



    def unfold_A(k):

        nonlocal result_dic, current_key, flag_loop, calculated_key, dic

        if k in result_dic:

            return set(result_dic[k])

        else:

            current_key.add(k)

            calculated_key.add(k)

            if type:

                result = set([])

            else:

                result = set(dic[k])

            for n in dic[k]:

                if n == k:

                    continue

                # print(n)

                if n in current_key:

                    flag_loop = True

                    # print(current_key)

                    continue

                if n in calculated_key:

                    if n in result_dic:

                        result.update(result_dic[n])

                    continue

                elif n not in dic:

                    result.add(n)

                else:

                    result.update(unfold_A(n))

            current_key.remove(k)

            if not current_key:

                flag_loop = False

                calculated_key = set([])

            if not flag_loop:

                if out:

                    result_dic[k] = list(result)

                else:

                    result_dic[k] = result

            # return list(result)

            return result



    for k in dic:

        assert current_key == set([])

        assert calculated_key == set([])

        assert flag_loop == False

        unfold_A(k)

    return result_dic             

import pandas as pd

# All following 3 functions are built in order to turn the ontology pool in a simple dictionnary :
                       
def dic_flatten(A2rB,B2rA,A2B,roles_inc):       #Flattens nested dict
    A2B_1 = A2B
    for key in A2rB.keys():
        for r in A2rB[key]:
            part_dict = A2rB[key]
            for B in part_dict[r]:
                key_str = B+'__'+r
                if key in A2B_1 :
                    A2B_1[key].add(key_str)
                else : 
                    A2B_1.update({key: {key_str}})
    for key in B2rA.keys():
        for r in B2rA[key]:
            part_dict = B2rA[key]
            for B in part_dict[r]:
                key_str = key+'__'+r
                if key_str in A2B_1 :
                    A2B_1[key_str].add(B)
                else : 
                    A2B_1.update({key_str : {B}})
            if r in roles_inc:
                for s in roles_inc[r]:
                    if key_str in A2B_1:
                        A2B[key_str].add(key+'__'+s)
    return(A2B_1)

def role_axioms_to_dict(role_axioms):    #takes roles axiom and turn them into a dict
    dict_1 = {}
    for i in role_axioms :
        key = split(i)[0]
        value = split(i)[1][0]
        if key not in dict_1:
            dict_1.update({key : {value}})
        else : 
            dict_1[key].add(value)
    return(dict_1)
 

def dict_axiom_RC(axioms_RC):       
    dict_RC = {}
    for i in axioms_RC :
        axiom_splitted = split(i)
        ax_1 = axiom_splitted[0]
        ax_2 = axiom_splitted[1][0]
        ax_composed = axiom_splitted[1][1]
        if ax_1 not in dict_RC:
            dict_RC.update({ax_1:{ax_2:{ax_composed}}})
        else :
            if ax_2 not in dict_RC[ax_1]:
                dict_RC.update({ax_1:{ax_2:{ax_composed}}})
            else:
                dict_RC[ax_1][ax_2].add(ax_composed)
    return(dict_RC)

                    
                
    
    
dic_test_A2B = {'A' : {'B','C','D'},'B':{'C','E'}}
dic_test_A2RB = {'A' : {'r':{'B'},'s':{'E'}},'C':{'r':{'A'}}}
dic_test_B2RA = {'A' : {'r':{'B','C'}}}
dic_test_role = {'r':'s'}


                        
def function_1(X,A,A2Ai,Ai2B,dict_simple):  #This is H1 
    dict_ax={}
                                            #double processing (pop puis add, faut delete au fur et a mesure)
    if A in A2Ai.keys():
        Ai_set_list = A2Ai[A]
        
        Ai_available = dict_simple[X]

        if Ai_set_list and Ai_available:
            for Ai_set in Ai_set_list:
                for Ai in Ai_set:
                    if Ai in Ai_available or Ai==X:
                        for Y in Ai2B[Ai_set]:
                                    if (X,Y) in dict_ax.keys():
                                        dict_ax[(X,Y)].add(((X,Ai_set),(Ai_set,A),(A,Y)))
                                    else:
                                        dict_ax.update({(X,Y):{((X,Ai_set),(Ai_set,A),(A,Y))}})
                                    
                    else:
                        break
    
    return(dict_ax)
    
    
    
    
def function_2(B1,B2,A2r2X,B2r2Y):   #H2 with B1 and B2
    dict_ax= {}
    if B1 in A2r2X.keys() and B2 in B2r2Y.keys():
        for r in A2r2X[B1]:
            if r in B2r2Y[B2].keys():
                for Y in B2r2Y[B2][r]:
                    for X in A2r2X[B1][r]:
                        if (X,Y) in dict_ax.keys():
                            dict_ax[(X,Y)].add(((X,r,B1),(B1,B2),(r,B2,Y)))
                        else:
                            dict_ax.update({(X,Y):{((X,r,B1),(B1,B2),(r,B2,Y))}})
    return(dict_ax)   
  
def function_3(r,B1,B2r2Y,dict_processed):  #H2 with B1 and r
    dict_ax ={}
    if B1 in dict_processed.keys():
            for B2 in dict_processed[B1]:
                if B2 in B2r2Y.keys():
                    if r in B2r2Y[B2]:
                        for Y in B2r2Y[B2][r]:
                            if (Y,) in dict_ax.keys():
                                dict_ax[(Y,)].add(((r,B1),(B1,B2),(r,B2,Y)))
                            else:
                                dict_ax.update({(Y,):{((r,B1),(B1,B2),(r,B2,Y))}})
    B11 = B1+'__'+r
    if B11 in dict_processed.keys():
        for B2 in dict_processed[B11]:
                if B2 in B2r2Y.keys():
                    if r in B2r2Y[B2]:
                        for Y in B2r2Y[B2][r]:
                            if (Y,) in dict_ax.keys():
                                dict_ax[(Y,)].add(((r,B1),(B1,B2),(r,B2,Y)))
                            else:
                                dict_ax.update({(Y,):{((r,B1),(B1,B2),(r,B2,Y))}})
        
    return(dict_ax)

def function_4(r,A1,H2rK,A2r2X,rs2t,B2r2Y,Original = None):  #H3 with r and A1
    dict_ax={}
    if r in rs2t.keys():
        if A1 in A2r2X.keys():
            if r in A2r2X[A1].keys():
                for s in rs2t[r]:
                    if A1 in H2rK.keys():
                        if s in H2rK[A1].keys():
                            for A2 in H2rK[A1][s]:
                                if A2 in B2r2Y.keys():
                                    for t in rs2t[r][s]:
                                        if t in B2r2Y[A2].keys():
                                            for Y in B2r2Y[A2][t]:
                                                if Original :
                                                    if (Original,Y) in dict_ax.keys():
                                                        dict_ax(Original,Y).add(((Original,r,A1),(A1,s,A2),(t,A2,Y)))
                                                    else:
                                                         dict_ax[(Original,Y)]={((Original,r,A1),(A1,s,A2),(t,A2,Y))}
                                                else:
                                                    for X in A2r2X[A1][r]:
                                                        if (X,Y) in dict_ax.keys():
                                                            dict_ax[(X,Y)].add(((X,r,A1),(A1,s,A2),(t,A2,Y)))
                                                        else:
                                                            dict_ax.update({(X,Y):{((X,r,A1),(A1,s,A2),(t,A2,Y))}})
    return(dict_ax)
            
    
def function_5(A1,A2,s,s2rt,B2r2Y,A2r2X):  #H3 with A1 and A2
    list_axioms=[]
    dict_ax={}
    if s in s2rt.keys():
        for r in s2rt[s]:
            for t in s2rt[s][r]:      
                if A2 in B2r2Y.keys() and A1 in A2r2X.keys():
                    if t in B2r2Y[A2] and r in A2r2X[A1]:
                        for Y in B2r2Y[A2][t]:
                            for X in A2r2X[A1][r]:
                                list_axioms.append((X,r,t,Y))
                                if (X,Y) in dict_ax.keys():
                                    dict_ax[(X,Y)].add(((X,r,A1),(A1,s,A2),(t,A2,Y)))
                                else:
                                    dict_ax.update({(X,Y):{((X,r,A1),(A1,s,A2),(t,A2,Y))}})
    return(dict_ax)   


def s2rt_r2st(s2rt):  #allow to witch the keys from r :s :t  to s:t:r
    r2st = {}
    for keys in s2rt.keys():
        for key in s2rt[keys]:
            if key in r2st.keys():
                if keys in r2st[key].keys():
                    r2st[key][keys].add(s2rt[keys][key])
                else:
                    r2st[key].update({keys : s2rt[keys][key]})
            else:
                r2st.update({key: {keys:s2rt[keys][key]}})
    return(r2st)
    
    
"""def add_axioms(X,Y,dic_init,dic_processed,S):
    if X not in dic_processed.keys():
                if '__' in Y:
                    split = Y.split('__')
                    A = split[0]
                    r = split[1]
                    if A in S.processed_pool.K2rH.keys():
                        if r in S.processed_pool.K2rH[A].keys():
                            S.processed_pool.K2rH[A][r].add(X)
                        else:
                            S.processed_pool.K2rH[A].update({r : {X}})
                    else:
                        S.processed_pool.K2rH.update({A:{r:{X}}})
                    if keys in S.processed_pool.H2rK.keys():   ##in order to be able to record clauses A: rB
                        if r in S.processed_pool.H2rK[X]:
                            S.processed_pool.H2rK[X][r].add(A)
                        else:
                            S.processed_pool.H2rK[X].update({r:{A}})
                    else:
                        S.processed_pool.H2rK.update({X:{r:{A}}})
                    
                else: 
                    if keys in S.processed_pool.H2A.keys():
                        S.processed_pool.H2A[X].add(Y)
                    else:
                        S.processed_pool.H2A.update({X:{Y}})
    else:
        if Y not in dic_processed[X]:
            if '__' in Y:
                    split = Y.split('__')
                    A = split[0]
                    r = split[1]
                    if A in S.processed_pool.K2rH.keys():
                        if r in S.processed_pool.K2rH[A].keys():
                            S.processed_pool.K2rH[A][r].add(X)
                        else:
                            S.processed_pool.K2rH[A].update({r : {X}})
                    else:
                        S.processed_pool.K2rH.update({A:{r:{X}}})
                    if keys in S.processed_pool.H2rK.keys():   ##in order to be able to record clauses A: rB
                        if r in S.processed_pool.H2rK[X]:
                            S.processed_pool.H2rK[X][r].add(A)
                        else:
                            S.processed_pool.H2rK[X].update({r:{A}})
                    else:
                        S.processed_pool.H2rK.update({X:{r:{A}}})
                    
            else: 
                    if keys in S.processed_pool.H2A.keys():
                        S.processed_pool.H2A[X].add(Y)
                    else:
                        S.processed_pool.H2A.update({X:{Y}})"""
            
            
        
    
def saturation_process(S,dic_init):
    dict_inferred ={}
    s2rt= dict_axiom_RC(S.ontology.axioms_RC)
    r2st= s2rt_r2st(s2rt)
    dic_processed={}
    while dic_init:
        
        dict_processed={}
        list_new_ax=[]
        A1 = sample(dic_init.keys(), 1)[0]
        if '__' in A1:
            
            split = A1.split('__')
            A = split[0]
            r = split[1]
            #list_connection_1= function_4(r,A,S.processed_pool.H2rK,S.processed_pool.K2rH,r2st,S.ontology_pool.B2rA)  #H3 with (r,A1) -> (X,A2,s,t,Y)
            list_connection_2 = function_3(r,A,S.ontology_pool.B2rA,S.processed_pool.H2A)   
                               #H2 with (r,B1) -> (B2,Y)
            if A in S.processed_pool.K2rH.keys() and r in S.processed_pool.K2rH[A].keys():
                for X in S.processed_pool.K2rH[A][r]:
                    if X in dic_processed.keys():
                        dic_processed[X].add(A1)
                    else:
                        dic_processed[X]={A1}
                    if X in dict_processed.keys():
                        dict_processed[X].add(A1)
                    else:
                        dict_processed[X]={A1}
                        
                    if list_connection_2:
                        for elem in list_connection_2.keys():
                            if X in dic_processed.keys():
                                if elem [0] not in dic_processed[X]:
                                    if X in dic_init.keys()and elem[0] not in dic_init[X]:
                                        dic_init[X].add(elem[0])
                                    else:
                                        dic_init[X]={elem[0]}
                            else:
                                if X in dic_init.keys()and elem[0] not in dic_init[X]:
                                    dic_init[X].add(elem[0])
                                else:
                                    dic_init[X]={elem[0]}
                
                    list_connection_3 = function_5(X,A,r,s2rt,S.ontology_pool.B2rA,S.processed_pool.K2rH)   #H3 with (A1,A2,S) -> (X,r,t,Y)
                    if list_connection_3:
                        for elem in list_connection_3.keys():
                            if elem[0] in dic_processed.keys():
                                if elem[1] not in dic_processed[elem[0]]:
                                    if elem[0] in dic_init.keys()and elem[1] not in dic_init[elem[0]]:
                                        dic_init[elem[0]].add(elem[1])
                                    elif elem[0] not in dic_init.keys():
                                        dic_init[elem[0]]={elem[1]}
                            else:
                                if elem[0] in dic_init.keys()and elem[1] not in dic_init[elem[0]]:
                                    dic_init[elem[0]].add(elem[1])
                                elif elem[0] not in dic_init.keys():
                                    dic_init[elem[0]]={elem[1]}
                            


                    list_connection_1= function_4(r,A,S.processed_pool.H2rK,S.processed_pool.K2rH,r2st,S.ontology_pool.B2rA) 
                    if list_connection_1:
                            for elem in list_connection_1.keys():  #mmmmh elem 0 ou x ?? (redondance entre function et appel ici)
                                if X in dic_processed.keys():
                                    if elem[1] not in dic_processed[X]:
                                        if X in dic_init.keys():
                                            dic_init[X].add(elem[1])
                                        else:
                                            dic_init[X]={elem[1]}
                                else:
                                    if X in dic_init.keys():
                                        dic_init[X].add(elem[1])
                                    else:
                                        dic_init[X]={elem[1]}
                    for keys in dict_processed.keys():
                        for elem in dict_processed[keys]:
                            
                            if '__' in elem:
                                split = elem.split('__')
                                A = split[0]
                                r = split[1]
                                if A in S.processed_pool.K2rH.keys():
                                    if r in S.processed_pool.K2rH[A].keys():
                                        S.processed_pool.K2rH[A][r].add(keys)
                                    else:
                                        S.processed_pool.K2rH[A].update({r : {keys}})
                                else:
                                    S.processed_pool.K2rH.update({A:{r:{keys}}})
                                if keys in S.processed_pool.H2rK.keys():   ##in order to be able to record clauses A: rB
                                    if r in S.processed_pool.H2rK[keys]:
                                        S.processed_pool.H2rK[keys][r].add(A)
                                    else:
                                        S.processed_pool.H2rK[keys].update({r:{A}})
                                else:
                                    S.processed_pool.H2rK.update({keys:{r:{A}}})
                                
                            else: 
                                if keys in S.processed_pool.H2A.keys():
                                    S.processed_pool.H2A[keys].add(elem)
                                else:
                                    S.processed_pool.H2A.update({keys:{elem}})
  
                                    
                                        
                    
  
 
        else:
                for elem in list(dic_init[A1]):
                    if A1 in dic_processed.keys():
                        dic_processed[A1].add(elem)
                    else:
                        dic_processed[A1]={elem}
                    if A1 in dict_processed.keys():
                            dict_processed[A1].add(elem)
                    else:
                        dict_processed[A1]={elem}
                    if '__' in elem:
                        
                        split = elem.split('__')
                        A2 = split[0]
                        s= split[1]
                        list_connection_1=function_4(s,A2,S.processed_pool.H2rK,S.processed_pool.K2rH,s2rt,S.ontology_pool.B2rA,A1)
                        list_connection_3=function_5(A1,A2,s,r2st,S.ontology_pool.B2rA,S.processed_pool.K2rH)
                        list_connection_2 = function_3(s,A2,S.ontology_pool.B2rA,S.processed_pool.H2A) 
                        if list_connection_3:
                            for elem in list_connection_3.keys():
                                if elem[0] in dic_processed.keys():
                                    if elem[1] not in dic_processed[elem[0]]:
                                        if elem[0] in dic_init.keys()and elem[1] not in dic_init[elem[0]]:
                                            dic_init[elem[0]].add(elem[1])
                                        elif elem[0] not in dic_init.keys():
                                            dic_init[elem[0]]={elem[1]}
                                else:
                                    if elem[0] in dic_init.keys()and elem[1] not in dic_init[elem[0]]:
                                        dic_init[elem[0]].add(elem[1])
                                    elif elem[0] not in dic_init.keys():
                                        dic_init[elem[0]]={elem[1]}
                                    
                        if list_connection_1:
                            for elem in list_connection_1.keys():
                                if elem[0] in dic_processed.keys():
                                    if elem[1] not in dic_processed[elem[0]]:
                                        if elem[0] in dic_init.keys()and elem[1] not in dic_init[elem[0]]:
                                            dic_init[elem[0]].add(elem[1])
                                        elif elem[0] not in dic_init.keys():
                                            dic_init[elem[0]]={elem[1]}
                                else:
                                    if elem[0] in dic_init.keys()and elem[1] not in dic_init[elem[0]]:
                                        dic_init[elem[0]].add(elem[1])
                                    elif elem[0] not in dic_init.keys():
                                        dic_init[elem[0]]={elem[1]}
                        if list_connection_2:
                                for elem in list_connection_2.keys():
                                    if A1 in dic_processed.keys():
                                        if elem[0] not in dic_processed[A1]:
                                            if A1 in dic_init.keys() and elem[0] not in dic_init[A1]:
                                                dic_init[A1].add(elem[0])
                                            elif A1 not in dic_init.keys():
                                                dic_init[A1]={elem[0]} 
                                    else:
                                        if A1 in dic_init.keys() and elem[0] not in dic_init[A1]:
                                            dic_init[A1].add(elem[0])
                                        elif A1 not in dic_init.keys():
                                            dic_init[A1]={elem[0]} 
                                        
                                        
                                        
                                        
                        
  
                        
      
                    else:

                        list_connection_4 = function_2(A1,elem,S.processed_pool.K2rH,S.ontology_pool.B2rA)   #H2 with (B1,B2) -> (X,r,Y)
                        list_connection_5 = function_1(A1,elem,S.ontology_pool.A2Ai,S.ontology_pool.Ai2B,dic_init)  #H1 with (X,{Ai}) -> (A0,Y)
                        if list_connection_4:
                            
                            for elem in list_connection_4.keys():
                                X=elem[0]
                                Y=elem[1]
                                if X in dic_processed.keys():
                                    if Y not in dic_processed[X]:
                                        if X in dic_init.keys()and Y not in dic_init[X]:
                                            dic_init[X].add(Y)
                                        elif X not in dic_init.keys():
                                            dic_init[X]={Y}
                                else:
                                    if X in dic_init.keys()and Y not in dic_init[X]:
                                        dic_init[X].add(Y)
                                    elif X not in dic_init.keys():
                                        dic_init[X]={Y}
                                        
                                    
   
                        if list_connection_5:
                            for elem in list_connection_5.keys():
                                X=elem[0]
                                Y=elem[1]
                                #print(X +' '+Y)
                                if X in dic_processed.keys():
                                    if Y not in dic_processed[X]:
                                        if X in dic_init.keys()and Y not in dic_init[X]:
                                            dic_init[X].add(Y)
                                        elif X not in dic_init.keys():
                                            dic_init[X]={Y}
                                else:
                                    if X in dic_init.keys()and Y not in dic_init[X]:
                                        dic_init[X].add(Y)
                                    elif X not in dic_init.keys():
                                        dic_init[X]={Y}
                                #print(dic_init)
                    for keys in dict_processed.keys():
                        for elem in dict_processed[keys]:
                            
                
                           
                            if '__' in elem:
                                split = elem.split('__')
                                A = split[0]
                                r = split[1]
                                if A in S.processed_pool.K2rH.keys():
                                    if r in S.processed_pool.K2rH[A].keys():
                                        S.processed_pool.K2rH[A][r].add(keys)
                                    else:
                                        S.processed_pool.K2rH[A].update({r : {keys}})
                                else:
                                    S.processed_pool.K2rH.update({A:{r:{keys}}})
                                if keys in S.processed_pool.H2rK.keys():   ##in order to be able to record clauses A: rB
                                    if r in S.processed_pool.H2rK[keys]:
                                        S.processed_pool.H2rK[keys][r].add(A)
                                    else:
                                        S.processed_pool.H2rK[keys].update({r:{A}})
                                else:
                                    S.processed_pool.H2rK.update({keys:{r:{A}}})
                                
                            else: 

                                if keys in S.processed_pool.H2A.keys():
                                    S.processed_pool.H2A[keys].add(elem)
                                else:
                                    S.processed_pool.H2A.update({keys:{elem}})
  
  

        processed_axiom = dic_init.pop(A1)

        for keys in dict_processed.keys():
            for elem in dict_processed[keys]:
                if keys in dic_init.keys():
                     if elem in dic_init[keys]:
                         dic_init[keys].remove(elem)

                
        for elem in processed_axiom:
           if A1 in dict_processed.keys():
               if elem not in dict_processed[A1]:
                   if A1 in dic_init.keys():
                       dic_init[A1].add(elem)
                   else:
                       dic_init[A1]={elem}
      
                
    return(S)
   # print(len(S.processed_pool.H2A)+len(S.processed_pool.H2rK)+len(S.processed_pool.K2rH))
   
   
def is_subdict(small, big):
    return dict(big, **small) == big
    
from deepdiff import DeepDiff    
 
if __name__=='__main__':
    list_dict = []
    start_time = time()
    dic_ontology = 'Ontologies-Less-Than-10000'
    dirs = os.listdir(dic_ontology)
    f1 = open(f'record_{dic_ontology}.csv', 'w')
    f1.write(f'name_ontology,num_axiom, num_non_el_axiom,load_time(s),saturate_time(s), num_generated_clause\n')
    #bool_test = True
    #d_test={'http://purl.obolibrary.org/obo/UBERON_0001034__http://purl.obolibrary.org/obo/nbo#by_means': {'http://www.absoluteiri.edu/RELAPPROXC2170'}, 'http://purl.obolibrary.org/obo/UBERON_0001033__http://purl.obolibrary.org/obo/nbo#by_means': {'http://www.absoluteiri.edu/RELAPPROXC2170'}, 'http://purl.obolibrary.org/obo/UBERON_0002203': {'http://purl.obolibrary.org/obo/UBERON_0001034'}, 'http://purl.obolibrary.org/obo/UBERON_0002204': {'http://purl.obolibrary.org/obo/UBERON_0001033'}, 'http://purl.obolibrary.org/obo/GO_0050881': {'http://www.absoluteiri.edu/RELAPPROXC2170'}, 'http://purl.obolibrary.org/obo/GO_0050882': {'http://www.absoluteiri.edu/RELAPPROXC2170'}}
    #print(type(d_test))
    for i, file in enumerate(dirs):
        print(f'\n\n{i}/{len(dirs)}th: {file}_________________________________')
        
        S= saturate(file[:-4])
        # print(S.ontology_pool.B2rA)
        roles_comp = dict_axiom_RC(S.ontology.axioms_RC)
        reversed_dictionary = {str(value) : key for (key, value) in S.ontology_pool.Ai2B.items()}
        roles_inc =role_axioms_to_dict(S.ontology.axioms_RI)
        s_t = time()
        d = dic_flatten(S.ontology_pool.A2rB,S.ontology_pool.B2rA,S.ontology_pool.A2B,roles_inc)
        d2 = unfold(d)
        """for keys in S.ontology_pool.Ai2B.keys():
            for elem in keys:
                if "2146" in elem:
                    print (keys)
                    print(S.ontology_pool.Ai2B[keys])"""
        S2 = saturation_process(S, d2)
        list_dict.append(S2)
        #print('a')
        #print(S2.processed_pool.H2A)
    
        
        #print(len(S.processed_pool.H2A.items())+len(S.processed_pool.H2rK.items())+len(S.processed_pool.K2rH.items()))
        
        #f1.write(f'{file},{num_axiom}, {num_non_el_axiom},{load_time},{saturate_time},{size_after_saturate}\n')
    
    #S1 = list_dict[0]
    #S2=list_dict[1]
  
    
          
    def list_diff(dic1,dic2):  
        list_diff=[]
        for keys in dic1:
            if keys in dic2.keys():
                for elem in dic1[keys]:
                    if elem not in dic2[keys]:
                        list_diff.append((keys,elem))
            else:
                for elem in dic1[keys]:
                    list_diff.append((keys,elem))
        if len(list_diff)>0 and len(list_diff)<100:
            print(list_diff)
        if len(list_diff)>99:
            print(list_diff[1:20])
        return(list_diff)
    print(len(S2.ontology_pool.A2Ai))
    print(len(S2.ontology_pool.Ai2B))
    #print(len(list_diff(S1.ontology_pool.A2B,S2.processed_pool.H2A)))
    #print(len(list_diff(S2.processed_pool.H2A,unfold(S2.processed_pool.H2A))))   
    for keys in S2.ontology_pool.A2Ai.keys():
        if keys == 'galen7.owl#ArteryWhichHasNoLaterality':
            print(S2.ontology_pool.A2Ai[keys])
        for elem in S2.ontology_pool.A2Ai[keys]:
            if elem == 'galen7.owl#ArteryWhichHasNoLaterality':
                print( keys +' '+elem)
    print('AI2B')    
    for keys in S2.ontology_pool.Ai2B.keys():
        if keys == 'galen7.owl#ArteryWhichHasNoLaterality':
            print(S2.ontology_pool.Ai2B[keys])
        for elem in S2.ontology_pool.Ai2B[keys]:
            if elem == 'galen7.owl#ArteryWhichHasNoLaterality':
                print( keys)
                print(elem)
            
    def longueur(dict1):
        cpt=0
        for keys in dict1.keys():
            for elem in dict1[keys]:
                cpt+=1
        return(cpt)
    print(longueur(S2.processed_pool.H2A))
    """print('q')
    print(S1.ontology_pool.Ai2B)
    print('a')
    print(S1.ontology_pool.A2Ai)
    print(len(S1.ontology_pool.A2B.items()))
    print(len(S2.processed_pool.H2A.items()))"""
    print('finished in', time() - start_time)
        
    
    
    
    
    
    
    
    
    