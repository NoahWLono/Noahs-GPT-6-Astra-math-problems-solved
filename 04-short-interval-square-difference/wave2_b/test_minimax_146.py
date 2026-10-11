#!/usr/bin/env python3
"""Independent cycling and fixture cases for the authorized supplemental bound."""
import importlib.util
from pathlib import Path
import unittest


class SupplementalCases(unittest.TestCase):
    def test_closed_extension(self):
        source = Path(__file__).with_name('generate_minimax_146.py')
        self.assertTrue(source.exists(), 'supplemental generator not implemented yet')
        spec = importlib.util.spec_from_file_location('generate_minimax_146', source)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        self.assertEqual(module.H, 146)
        self.assertEqual(module.fixture_counts(1, 0, 146), [146])
        self.assertEqual(module.fixture_counts(4, 3, 146), [73] * 4)
        self.assertEqual(max(module.fixture_counts(9, 7, 146)), 34)
        self.assertEqual(max(module.fixture_counts(16, 13, 146)), 37)
        self.assertEqual(module.fixture_counts(9, 7, 2), [0, 0, 0, 1, 2, 1, 0, 0, 0])
        with self.assertRaises(ValueError):
            module.fixture_counts(144, 1, 147)


if __name__ == '__main__':
    unittest.main()
