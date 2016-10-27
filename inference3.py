import collections
import copy
import sys

__author__ = 'Ajay'


kb = collections.OrderedDict()
queries = collections.OrderedDict()


def standardize(clause, i):
    retval = clause[:clause.find('(')+1]
    args = fetch_arguments_as_list(clause)
    for v in args:
        if variable_check(v):
            retval += v + str(i) + ','
        else:
            retval += v + ','
    retval = retval[:len(retval)-1]
    retval += ')'
    return retval


def build_queries_and_kb():
    file_name='input.txt'
    # file_name = sys.argv[2]
    # if '.txt' not in file_name:
    #     file_name += '.txt'
    file = open(file_name, 'r')
    queries_count = file.readline()
    for i in range(0, int(queries_count)):
        queries[file.readline().strip()] = False

    clauses_count = file.readline()
    for i in range(0, int(clauses_count)):
        clause = file.readline().strip()
        if '=' in clause:
            split_clause = clause.split('=>')
            for j in range(0, len(split_clause)):
                clause_split = split_clause[j].split('^')
                temp = []
                for s in clause_split:
                    temp.append(standardize(s, i))
                split_clause[j] = "^".join(temp)
            if split_clause[1].strip() in kb.keys():
                lst = kb[split_clause[1].strip()]
                lst.append(split_clause[0].strip())
                kb[split_clause[1].strip()] = lst
            else:
                kb[split_clause[1].strip()] = [split_clause[0].strip()]
        else:
            if clause in kb.keys():
                kb[clause].append(True)
            else:
                kb[clause] = [True]
    file.close()


def unify(x, y, subslist):
    x = x.strip()
    y = y.strip()

    if subslist is False:
        return False

    temp_subs = dict.copy(subslist)

    if x == y:
        return temp_subs

    elif variable_check(x):
        return unify_var(x, y, temp_subs)

    elif variable_check(y):
        return unify_var(y, x, temp_subs)

    elif compound_check(x) and compound_check(y):
        return unify(fetch_arguments(x), fetch_arguments(y), unify(extract_operator(x), extract_operator(y), temp_subs))

    elif list_check(x) and list_check(y):
        return unify(fetch_rest(x), fetch_rest(y), unify(fetch_first(x), fetch_first(y), temp_subs))

    else:
        return False


def variable_check(x):
    x = x.strip()
    if x[0].islower():
        for i in range(1, len(x)):
            if x[i] not in ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']:
                return False
        return True
    else:
        return False


def variable_check_initial(x):
    x = x.strip()
    if len(x) == 1 and x.islower():
        return True
    else:
        return False


def compound_check(x):
    if x.find('(') != -1:
        return True
    else:
        return False


def list_check(x):
    if ',' in x:
        return True
    else:
        return False


def fetch_arguments(x):
    x = x.strip()
    return x[x.index('(') + 1: len(x) - 1]


def fetch_arguments_as_list(x):
    args = fetch_arguments(x)
    return args.split(',')


def fetch_variables(x):
    var = []
    for a in fetch_arguments(x).split(','):
        if len(a) == 1:
            if variable_check_initial(a.strip()):
                var.append(a.strip())
        if len(a) == 2:
            if variable_check(a.strip()):
                var.append(a.strip())
    return var


def extract_operator(x):
    x = x.strip()
    op = x[0:x.index('(')]
    return op


def fetch_first(x):
    x = x[0: x.index(',')]
    return x.strip()


def fetch_rest(x):
    x = x[x.index(',') + 1: len(x)]
    return x.strip()


def unify_var(var, x, subslist):
    if var in subslist.keys():
        return unify(subslist[var], x, subslist)
    elif x in subslist.keys():
        return unify(var, subslist[x], subslist)
    elif occur_check(var, x, subslist):
        return False
    elif compound_check(x):
        subres = substitute(var, x, subslist)
        if not subres:
            return False
        else:
            return subslist
    else:
        subslist[var] = x
        return subslist


def substitute(var, x, subslist):
    args = fetch_arguments(x)
    for a in args:
        if compound_check(a):
            substitute(var, x, subslist)
        elif variable_check(a):
            if a in subslist.keys():
                substitution_value = subslist[a]
                subslist[var] = x.replace(x[x.find('(') + 1: x.find(')')], substitution_value)
                return subslist
            else:
                return False


def occur_check(var, x, s):
    if var == x:
        return True
    elif variable_check(x) and x in s:
        return occur_check(var, s[x], s)
    elif compound_check(x):
        return occur_check(var, extract_operator(x), s) or occur_check(var, fetch_arguments(x), s)
    else:
        return False


fact = []


def fol_bc_ask(query):
    fact.clear()
    return fol_bc_or(query, {})


def fol_bc_or(goal, theta):
    goal = goal.strip()
    unify_list = []
    match_found = False

    if goal in fact:
        theta['Failed'] = 'Failed'
        unify_list.append(theta)
        return unify_list

    # if has_variables(goal) is False:
    fact.append(goal)

    if goal in kb and True in kb[goal]:
        fact.remove(goal)
        theta['Found'] = 'Found'
        unify_list.append(theta)
        return unify_list

    for key in kb.keys():
        if extract_operator(key) == extract_operator(goal):
            match_found = True
            for value in kb[key]:
                result = {}
                unifier = unify(key, goal, {})
                if unifier is False:
                    result['Failed'] = 'Failed'
                else:
                    if value is not True:
                        result = fol_bc_and(value.split('^'), unifier)
                    else:
                        result = fol_bc_and(goal.split('^'), unifier)
                    result.update(unifier)
                if 'Found' in result and 'Failed' not in result:
                    if goal in fact:
                        fact.remove(goal)
                    result.update(theta)
                    unify_list.append(result)
    if not match_found or not unify_list:
        theta['Failed'] = 'Failed'
        unify_list.append(theta)
    return unify_list


# noinspection PyUnusedLocal
def fol_bc_and(querys, theta):
    if theta:
        if 'Failed' in theta:
            return theta
    if not querys:
        return theta

    first = get_first(querys)
    first = unifier_substitution(theta, first)
    or_res = fol_bc_or(first, theta)
    rest = get_rest(querys)
    error = True
    for res in or_res:
        if rest and 'Failed' not in res:
            fol_bc_and(rest, res)
        if 'Failed' not in res and 'Found' in res:
            theta.update(res)
            error = False
            # return res
    if error:
        theta['Failed'] = 'Failed'
    return theta


def get_first(x):
    return x[0]


def get_rest(x):
    temp = copy.deepcopy(x)
    temp.pop(0)
    return temp


def unifier_substitution(subslist, x):
    retval = x[:x.find('(')+1]
    args = fetch_arguments_as_list(x)
    for a in args:
        a = a.strip()
        if compound_check(a):
            unifier_substitution(subslist, a)
        else:
            if variable_check(a):
                if a in subslist.keys():
                    value = subslist[a]
                    if variable_check(value) and value in subslist:
                        value = subslist[value]
                    retval += value + ','
                else:
                    retval += a + ','
            else:
                retval += a + ','
    retval = retval[:len(retval)-1]
    retval += ')'
    return retval


def has_variables(x):
    if len(fetch_variables(x)) == 0:
        return False
    else:
        return True


def main():
    try:
        file = open('output.txt', 'w')
        build_queries_and_kb()
        for q in queries:
            try:
                result_list = fol_bc_ask(q)
                if 'Found' in result_list[0] and 'Failed' not in result_list[0]:
                    file.write('TRUE' + '\n')
                    print('TRUE')
                else:
                    file.write('FALSE' + '\n')
                    print('FALSE')
            except:
                file.write('FALSE' + '\n')
                print('FALSE')
        file.close()
    except:
        print("Unexpected error:", sys.exc_info()[0])


main()
