# Copyright (c) 2019 jianfeng
#
# This software is released under the MIT License.
# https://opensource.org/licenses/MIT

from copy import deepcopy
import pdb

# Partial Persistence [Driscoll, Saransk, Sleator, Tarjan - JCSS1989].

# What is partial persistence?
#     Only the latest version can be updated
#     Versions linearly order

# Any pointer-machine DS with $\le p=O(1)$ pointers to any node (in any version)
#     can be made partially persistent
#     with O(1) amoritized multiplicative overhead AND
#     O(1) space per change

# This file implements the two types of DS
#     - Linkedlist. Field={val, n_ptr}
#     - BST -- binary search Tree. Field={val, l_ptr r_ptr}


class PartialPersistentNode():
    def __init__(self, data_vars_tags, ptr_vars_tags, max_pointer_num=1):
        self.p, self.dt, self.pt = max_pointer_num, data_vars_tags, ptr_vars_tags

        self.fields = {var: None for var in self.dt + self.pt}
        self.back = {var: set() for var in self.pt}
        self.mods = list()  # list of tuple (version, field, value)

    def read(self, var, v):
        assert var in self.fields.keys()

        res = self.fields[var]
        for (mod_version, mod_field, mod_value) in self.mods:
            if mod_version > v: break
            if mod_field == var: res = mod_value
        return res

    def set_back(self, ptr, new, old=None):
        assert ptr in self.pt
        if old is not None and old in self.back[ptr]:
            self.back[ptr].remove(old)
        self.back[ptr].add(new)

    def write(self, now, var, val):
        assert var in self.fields.keys()
        if len(self.mods) <= 2 * self.p:
            self.mods.append((now, var, val))
        else:
            # crate the new node. save the latest value
            new = PartialPersistentNode(self.dt, self.pt, self.p)
            for (_, mod_field, mod_value) in self.mods:
                new.fields[mod_field] = mod_value
            new.fields[var] = val
            new.back = {
                var: set([i for i in self.back[var]])
                for var in self.pt
            }

            # change to backpoints in pointingto
            for ptr in self.pt:
                node_pointing_to = new.fields[ptr]
                node_pointing_to.set_back(ptr, new, self)

            # recursively change pointers to self -> new (found vai back pointers)
            for ptr in self.pt:
                for node_point_to_me in new.back[ptr]:
                    node_point_to_me.write(now, ptr, new)


class LinkedList():
    def __init__(self):
        self.dt, self.pt, self.p = ['value'], ['next_ptr'], 1
        self.root = PartialPersistentNode(self.dt, self.pt, self.p)
        self._timestamp = 0

    def now(self):  # equivalent to  (++now)
        res = self._timestamp
        self._timestamp += 1
        return res

    def set_root_value(self, val):
        self.root.write(self.now(), 'value', val)

    def append(self, val):
        at = self.now()
        cursor = self.root
        while True:
            next_node = cursor.read('next_ptr', at)
            if next_node is None:
                break
            else:
                cursor = next_node

        new = PartialPersistentNode(self.dt, self.pt, self.p)
        new.write(at, 'value', val)
        new.set_back('next_ptr', cursor)
        cursor.write(at, 'next_ptr', new)
        return self

    def modify_ith_node_val(self, i, val):
        assert i >= 0
        at = self.now()
        cursor = self.root
        for _ in range(i):
            cursor = cursor.read('next_ptr', at)
            if cursor is None:
                self.append(val)
                return self
        cursor.write(at, 'value', val)

        return self

    def insert_after_ith_node(self, i, val):
        at = self.now()
        cursor = self.root
        for _ in range(i):
            cursor = cursor.read('next_ptr', at)
            if cursor is None:
                self.append(val)
                return self
        next_ = cursor.read('next_ptr', at)

        new = PartialPersistentNode(self.dt, self.pt, self.p)
        new.write(at, 'value', val)

        cursor.write(at, 'next_ptr', new)
        new.write(at, 'next_ptr', next_)

        next_.set_back('next_ptr', new, cursor)
        new.set_back('next_ptr', cursor)

        return self

    def delete_ith_node(self, i):
        assert i > 0, "Assuming do not delete the root"
        at = self.now()
        cursor = self.root
        for _ in range(i - 1):  # move the one before what
            cursor = cursor.read('next_ptr', at)
            if cursor is None: return self

        next_ = cursor.read('next_ptr', at)
        next_next = next_.read('next_ptr', at)
        cursor.write(at, 'next_ptr', next_next)
        next_next.set_back('next_ptr', cursor, next_)

        return self

    def str_(self, v):
        res = ""
        cursor = self.root
        while cursor:
            res += str(cursor.read('value', v)) + '->'
            cursor = cursor.read('next_ptr', v)
        res += 'END'
        return res

    def __str__(self):
        return self.str_(self._timestamp)


if __name__ == '__main__':
    L = LinkedList()
    L.set_root_value(1)
    L.append(2).append(3).append(4).append(5)
    cp1 = L.now()  # checkpoint 1
    print(f'Current time = {cp1}, Latest linked list shows as {L}')

    L.modify_ith_node_val(2, 20)
    cp2 = L.now()
    print(f'Current time = {cp2}, Latest linked list shows as {L}')

    L.insert_after_ith_node(2, 22)

    cp3 = L.now()
    print(f'Current time = {cp3}, Latest linked list shows as {L}')

    L.modify_ith_node_val(1, 10)
    cp4 = L.now()
    print(f'Current time = {cp4}, Latest linked list shows as {L}')

    L.delete_ith_node(2)
    cp5 = L.now()
    print(f'Current time = {cp5}, Latest linked list shows as {L}')

    print("\n\nRolling back to earliest check points")
    for cp in [cp5, cp4, cp3, cp2, cp1]:
        print(f'In {cp}, list shows as {L.str_(cp)}')

# >>> STDOUT
# Current time = 5, Latest linked list shows as 1->2->3->4->5->END
# Current time = 7, Latest linked list shows as 1->2->20->4->5->END
# Current time = 9, Latest linked list shows as 1->2->20->22->4->5->END
# Current time = 11, Latest linked list shows as 1->10->20->22->4->5->END
# Current time = 13, Latest linked list shows as 1->10->22->4->5->END

# Rolling back to earliest check points
# In 13, list shows as 1->10->22->4->5->END
# In 11, list shows as 1->10->20->22->4->5->END
# In 9, list shows as 1->2->20->22->4->5->END
# In 7, list shows as 1->2->20->4->5->END
# In 5, list shows as 1->2->3->4->5->END