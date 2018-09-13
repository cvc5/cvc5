#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright (C) 2016  Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA

from __future__ import with_statement  # Required in 2.5
from __future__ import print_function

from verifier import *
import unittest


class Map(dict):
    """
    Example:
    m = Map({'first_name': 'Eduardo'}, last_name='Pool', age=24, sports=['Soccer'])
    """
    def __init__(self, *args, **kwargs):
        super(Map, self).__init__(*args, **kwargs)
        for arg in args:
            if isinstance(arg, dict):
                for k, v in arg.items():
                    self[k] = v

        if kwargs:
            for k, v in kwargs.iteritems():
                self[k] = v

    def __getattr__(self, attr):
        return self.get(attr)


class TestVerifier(unittest.TestCase):
    def setUp(self):
        options = Map({"verbose": False, "maxtime": 60, "maxtimediff": 160})
        self.s = solution_parser(options)

    def test_sat_cl(self):
        self.assertTrue(self.s._check_regular_clause("1 2 3", {1: True}))
        self.assertTrue(self.s._check_regular_clause("1 2 3", {2: True}))
        self.assertTrue(self.s._check_regular_clause("1 2 -3", {3: False}))

    def test_unsat_cl(self):
        self.assertRaises(NameError, self.s._check_regular_clause, "-1 2 3", {1: True})
        self.assertRaises(NameError, self.s._check_regular_clause, "-1 2 3", {})
        self.assertRaises(NameError, self.s._check_regular_clause, "-1 2 3 0", {})
        self.assertRaises(NameError, self.s._check_regular_clause, "1 2 -3 0", {0: True})
        self.assertRaises(NameError, self.s._check_regular_clause, "1 2 3", {1: False, 2: False, 3: False})
        self.assertRaises(NameError, self.s._check_regular_clause, "-1 -2 -3", {1: True, 2: True, 3: True})

    def test_sat_xcl(self):
        self.assertTrue(NameError, self.s._check_xor_clause("x1 2 3", {1: True, 2: False, 3: False}))
        self.assertTrue(NameError, self.s._check_xor_clause("x1 2 3 0", {1: True, 2: False, 3: False}))

    def test_unsat_xcl(self):
        self.assertRaises(NameError, self.s._check_xor_clause, "x1 2 3", {1: True})
        self.assertRaises(NameError, self.s._check_xor_clause, "x1 2 3", {1: False, 2: False, 3: False})

    def test_sol_parse_sat(self):
        unsat, s, _ = self.s.parse_solution_from_output(["s SAT", "v 1 2 3 0"])
        self.assertEqual(s, {1: True, 2: True, 3: True})

    def test_sol_parse_unsat(self):
        unsat, _, _ = self.s.parse_solution_from_output(["s UNSAT\n"])
        self.assertTrue(unsat)


if __name__ == '__main__':
    unittest.main()
