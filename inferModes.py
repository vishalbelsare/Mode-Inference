"""inferModes.py: A prototype Python package for minimizing the size of datasets,
                  inferring datatypes, and converting them into a relational schema.

BSD 2-Clause License

Copyright (c) 2018, Alexander L. Hayes
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright notice,
  this list of conditions and the following disclaimer in the documentation
  and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."""



from __future__ import print_function
from collections import Counter
from copy import deepcopy
from random import choice
import argparse
import re



__author__ = "Alexander L. Hayes (@batflyer)"
__copyright__ = "Copyright 2018, Alexander L. Hayes"
__credits__ = ["Alexander L. Hayes", "Kaushik Roy", "Sriraam Natarajan"]

__license__ = "BSD 2-Clause"
__version__ = "0.2.0"
__maintainer__ = "Alexander L. Hayes (@batflyer)"
__email__ = "alexander@batflyer.net"
__status__ = "Prototype"



# A regular expression which verifies whether or not modes are formatted properly.
_instance_re = re.compile(r'[a-zA-Z0-9]*\(([a-zA-Z0-9]*,( )*)*[a-zA-Z0-9]*\)\.')



class SetupArguments:
    """
    @batflyer: I am maintaining these as classes in the event that this reaches a point where I convert it into a package.
    """

    def __init__(self, verbose=False, positive=None, negative=None, facts=None):
    
        parser = argparse.ArgumentParser(description='Minimizing positives, negatives, and facts, and performing mode inference', epilog="Copyright 2018 Alexander L. Hayes. BSD 2-Clause. A full copy of the license is available at the head of the source. The text can also be found online <https://opensource.org/licenses/BSD-2-Clause>.")
        parser.add_argument("-v", "--verbose", help="Increase verbosity to help with debugging.", default=verbose, action="store_true")
        parser.add_argument("-pos", "--positive", help="Path to positive examples.", type=str, default=positive)
        parser.add_argument("-neg", "--negative", help="Path to negative examples.", type=str, default=negative)
        parser.add_argument("-fac", "--facts", help="Path to relational facts.", type=str, default=facts)
        
        self.args = parser.parse_args()


        
class InferenceUtils:
    """
    A set of utilities useful for the inferModes module.
    """

    def __init__(self):
        pass

    @staticmethod
    def inspect_instance_syntax(example):
        """
        Uses a regular expression to check whether or not a mode is formatted correctly.
          Example:
             friends(Alice, Bob).   :::   pass
             friends(Bob, Alice).   :::   pass
             smokes(Bob).           :::   pass
        
             useStdLogicVariables   :::   fail
             friends).              :::   fail
        """
        if not _instance_re.search(example):
            raise Exception('Error when checking ground instances; incorrect syntax: ' + example)

    @staticmethod
    def parse(predicate_string):
        """
        Input a string of the format: 'father(harrypotter,jamespotter).'

        Ensures syntax is correct, then returns a list where [0] is the name of the literal
        and [1] is a list of variables in the rule.
           ['father', ['harrypotter', 'jamespotter']]
        """
        InferenceUtils.inspect_instance_syntax(predicate_string)
        
        predicate_list = predicate_string.replace(' ', '').split(')', 1)[0].split('(')
        predicate_list[1] = predicate_list[1].split(',')
        return predicate_list

    @staticmethod
    def read(path):
        """
        Reads the data from file located at 'path', returns a list of strings where each
        string contains the information on that particular line.

        Raises an exception if the data cannot be read.
        """
        try:
            with open(path) as f:
                data = f.read().splitlines()
            return data
        except:
            raise Exception('Could not open file, no such file or directory.')

    @staticmethod
    def ground_predicate_strings_to_ground_predicate_lists(list_of_strings):
        """
        Convert a list of ground predicate strings into a list of ground predicate lists.
        
        For example:
             ['f(a1,a2).', 'f(a2,a3).', ...] ==> [['f', ['a1', 'a2']], ['f', ['a2', 'a3']]]
        """
        return list(map(InferenceUtils.parse, list_of_strings))

    @staticmethod
    def sort_keys(pos, neg, fac):
        """
        Input:
        pos: a list of lists representing positive ground predicates.
        neg: a list of lists representing negative ground predicates.
        fac: a list of lists representing factual ground predicates.

        (See `ground_predicate_strings_to_ground_predicate_lists` to construct these lists)

        Counts the number of occurances of each item in the head and body of the ground predicates.
        These keys are mapped to integer values, where lower numbers represent more common items.
        
        Returns two dictionaries:
        1. predicate_head_index: maps identifier to key e.g. `{'father': 0, 'childof': 1, 'male': 2, ...}`
        2. predicate_body_index: maps object to key. e.g. `{'ron': 0, 'george': 1, 'fred': 2, ...}`
        """

        # Count each grounding in the head and body.
        def invert_keys():
            head_cnt = Counter()
            body_cnt = Counter()
            
            for data in pos + neg + fac:
                head_cnt[data[0]] += 1
                for i in data[1]:
                    body_cnt[i] += 1

            # Invert the counts: that which is most common gets the lowest number.
            head_cnt_srt = sorted(head_cnt, key=head_cnt.get, reverse=True)
            body_cnt_srt = sorted(body_cnt, key=body_cnt.get, reverse=True)

            clause_head = {}
            clause_body = {}

            # Turn this order into a dictionary so we can query it later.
            for i in range(len(head_cnt)):
                clause_head[head_cnt_srt[i]] = i
            for i in range(len(body_cnt)):
                clause_body[body_cnt_srt[i]] = i
            return clause_head, clause_body

        predicate_head_index, predicate_body_index = invert_keys()
        return predicate_head_index, predicate_body_index

    @staticmethod
    def compress_ground_predicates(dataset, predicate_head_index, predicate_body_index):
        """
        Compress the clauses into a list that can be written to a file.
        """
        ground_predicate_list = []
        for data in dataset:
            new_predicate = ''
            new_predicate += str(predicate_head_index[data[0]]) + ','
            for b in range(len(data[1])):
                if b == (len(data[1]) - 1):
                    new_predicate += str(predicate_body_index[data[1][b]])
                else:
                    new_predicate += str(predicate_body_index[data[1][b]]) + ','
            ground_predicate_list.append(new_predicate)
        return ground_predicate_list
    
def compress_clauses(pos, neg, fac):
    """
    pos: a list of strings representing positive literals.
    neg: a list of strings representing negative literals.
    fac: a list of strings representing facts.
    
    Returns: 
    """

    predicate_head_index, predicate_body_index = InferenceUtils.sort_keys(pos, neg, fac)
    
    new_pos = InferenceUtils.compress_ground_predicates(pos, predicate_head_index, predicate_body_index)
    new_neg = InferenceUtils.compress_ground_predicates(neg, predicate_head_index, predicate_body_index)
    new_fac = InferenceUtils.compress_ground_predicates(fac, predicate_head_index, predicate_body_index)

    return new_pos, new_neg, new_fac

def compress_to_sets(pos, neg, fac):
    """
    Converts the predicates from a dataset into a dictionary where each key represents the head of
    a predicate, and the value is a list of sets. Each set represents all of the objects at a
    certain position of the ground predicate.

    For example:
        Begin    -> {}
        ...
        0(5,13). -> {'0': [{5}, {13}]}
        0(6,8).  -> {'0': [{5, 6}, {8, 13}]}
        0(3,4).  -> {'0': [{3, 5, 6}, {4, 8, 13}]}
        1(3,4).  -> {'1': [{3}, {4}], '0': ... }
        ...
        End      -> {'0': ..., '1': ..., ...}

    Input:
    pos: a list of strings representing positive literals.
    neg: a list of strings representing negative literals.
    fac: a list of strings representing facts.

    Returns: a dictionary.
    """
    set_dictionary = {}

    # Create the keys for the head and body of the predicates.
    predicate_head_index, predicate_body_index = InferenceUtils.sort_keys(pos, neg, fac)

    # TENTATIVELY PRINT THIS TO VERIFY SOME RESULTS.
    print(predicate_head_index)
    #print(predicate_body_index)
    
    for data in pos + neg + fac:

        key = str(predicate_head_index[data[0]])

        if key not in set_dictionary:
            # The head of the ground predicate has not been seen before.
            set_dictionary[key] = []

            # Set the value to a list of sets (number of sets = len(data[1]))
            for _ in range(len(data[1])):
                set_dictionary[key].append(set())

        # Each object in the body of the predicate is unioned to the set that has been observed.
        for obj_index in range(len(data[1])):
            obj = set([str(predicate_body_index[data[1][obj_index]])])
            set_dictionary[key][obj_index] = set_dictionary[key][obj_index].union(obj)
    
    return set_dictionary

class Types:
    """
    Types are represented by integers. The maximum number of types (n) should
    occur when every object is of a different type.
    """

    def __init__(self, n):
        self.i = 0
        self.n = n

    def __iter__(self):
        return self
    
    def next(self):
        if self.i < self.n:
            i = self.i
            self.i += 1
            return i
        else:
            raise StopIteration()

class Predicate:

    def __init__(self, key, object_set):
        self.key = key
        self.object_set = object_set
        self._type = None

    def __repr__(self):
        return self.key

def PredicateLogicTypeInference(untyped_dict):
    """
    Input: a set_dictionary (see `compress_to_sets`)

    ['0_0', {'2', '3', '6', '8'}, None]
    """

    print(untyped_dict)

    untyped = []
    for key in untyped_dict:
        for i in range(len(untyped_dict[key])):
            untyped.append([str(key) + '_' + str(i), untyped_dict[key][i], None])

    var = Types(len(untyped))
    typed = []

    while untyped:

        # Choose a random set from untyped.
        c = choice(untyped)

        # Declare the type of the set.
        c[2] = var.next()

        untyped.remove(c)
        typed.append(c)

        unknownTypes = deepcopy(untyped)
        for unknownType in unknownTypes:

            if c[1].intersection(unknownType[1]):
                
                untyped.remove(unknownType)
                unknownType[2] = c[2] # unknownType.type = c.type
                typed.append(unknownType)

    return typed

def __main():

    # Read the arguments from the commandline.
    args = SetupArguments().args
    
    # Use the 'read' utility to read positives, negatives, and facts.
    pos = InferenceUtils.read(args.positive)
    neg = InferenceUtils.read(args.negative)
    fac = InferenceUtils.read(args.facts)

    # Use the 'ground_predicate_strings_to_ground_predicate_lists' utility to convert them.
    pos = InferenceUtils.ground_predicate_strings_to_ground_predicate_lists(pos)
    neg = InferenceUtils.ground_predicate_strings_to_ground_predicate_lists(neg)
    fac = InferenceUtils.ground_predicate_strings_to_ground_predicate_lists(fac)

    #pos, neg, fac = compress_clauses(pos, neg, fac)

    set_dictionary = compress_to_sets(pos, neg, fac)
    #print(set_dictionary)
    
    output = PredicateLogicTypeInference(set_dictionary)
    for i in output:
        print(i[0], i[2])

if __name__ == '__main__':
    __main()
