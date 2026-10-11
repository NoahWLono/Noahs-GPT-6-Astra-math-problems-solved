#!/usr/bin/env python3
"""Hand-derived fixed cases, written before the exhaustive implementation."""
import importlib.util
from pathlib import Path
import unittest


class FixedCases(unittest.TestCase):
    def test_hand_cases_and_bounds(self):
        source = Path(__file__).with_name('generate_minimax.py')
        self.assertTrue(source.exists(), 'closed minimax generator not implemented yet')
        spec = importlib.util.spec_from_file_location('generate_minimax', source)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        self.assertEqual(module.fixture_counts(1, 0, 64), [64])
        self.assertEqual(module.fixture_counts(4, 1, 2), [1, 1, 1, 1])
        self.assertEqual(module.fixture_counts(4, 3, 9), [5, 4, 5, 4])
        self.assertEqual(module.fixture_counts(9, 7, 2), [0, 0, 0, 1, 2, 1, 0, 0, 0])
        self.assertEqual(module.fixture_counts(16, 13, 8), [2] * 16)
        for args in ((257, 1, 2), (0, 0, 2), (4, 2, 2), (1, 1, 1), (4, 1, 65)):
            with self.assertRaises(ValueError):
                module.fixture_counts(*args)


if __name__ == '__main__':
    unittest.main()
