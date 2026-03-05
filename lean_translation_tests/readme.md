# MiniZinc to Lean Translation Tests

This directory contains the test cases and results for the MiniZinc to Lean 4 translation. The subdirectories are structured as follows:
- `./source_files` contain the original MiniZinc files. Each one consists of a base model and one or several `redundant` or `nonredundant` constraints that each represent one test case.
- `./targets_minizinc` are the MiniZinc models used to verify that MiniZinc + Chuffed behave as expected on the test cases.
- `./targets_and_proofs_lean` contains the MiniZinc input files for the Lean translation, the finished theorems and, where applicable, the discovered proof. A proof was found for all positive (redundant) cases and no proof was found for any negative (nonredundant) case.

## Detailed Results

| Source File | Test Case ID | Pos/Neg | Lean Result | Minizinc Result |
|---|---|---|---|---|
| arithmetic_bool1.mzn | base | base | - | MINIZINC OK |
| arithmetic_bool1.mzn | 0 | pos | PROVEN | MINIZINC OK |
| arithmetic_bool1.mzn | 1 | pos | PROVEN | MINIZINC OK |
| arithmetic_bool1.mzn | 2 | pos | PROVEN | MINIZINC OK |
| arithmetic_bool1.mzn | 3 | pos | PROVEN | MINIZINC OK |
| arithmetic_bool1.mzn | 4 | pos | PROVEN | MINIZINC OK |
| arithmetic_bool1.mzn | 5 | pos | PROVEN | MINIZINC OK |
| arithmetic_bool2.mzn | base | base | - | MINIZINC OK |
| arithmetic_bool2.mzn | 0 | pos | PROVEN | MINIZINC OK |
| arithmetic_bool2.mzn | 1 | pos | PROVEN | MINIZINC OK |
| arithmetic_bool2.mzn | 2 | pos | PROVEN | MINIZINC OK |
| arithmetic_bool2.mzn | 3 | pos | PROVEN | MINIZINC OK |
| arithmetic_ifthenelse.mzn | base | base | - | MINIZINC OK |
| arithmetic_ifthenelse.mzn | 0 | pos | PROVEN | MINIZINC OK |
| arithmetic_ifthenelse.mzn | 1 | pos | PROVEN | MINIZINC OK |
| arithmetic_ifthenelse_elseif.mzn | base | base | - | MINIZINC OK |
| arithmetic_ifthenelse_elseif.mzn | 0 | pos | PROVEN | MINIZINC OK |
| arithmetic_ifthenelse_elseif.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| arithmetic_int.mzn | base | base | - | MINIZINC OK |
| arithmetic_int.mzn | 0 | pos | PROVEN | MINIZINC OK |
| arithmetic_int.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| arrays_collapsed_literals_and_views.mzn | base | base | - | MINIZINC OK |
| arrays_collapsed_literals_and_views.mzn | 0 | pos | PROVEN | MINIZINC OK |
| arrays_collapsed_literals_and_views.mzn | 1 | pos | PROVEN | MINIZINC OK |
| arrays_collapsed_literals_and_views.mzn | 2 | pos | PROVEN | MINIZINC OK |
| arrays_collapsed_literals_and_views.mzn | 3 | pos | PROVEN | MINIZINC OK |
| arrays_collapsed_literals_and_views.mzn | 4 | pos | PROVEN | MINIZINC OK |
| arrays_collapsed_literals_and_views.mzn | 5 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_all_different.mzn | base | base | - | MINIZINC OK |
| constraint_all_different.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_all_different.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_all_different.mzn | 2 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_array2d_bool_aggregators.mzn | base | base | - | MINIZINC OK |
| constraint_array2d_bool_aggregators.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_array2d_bool_aggregators.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_array2d_min_max_plain.mzn | base | base | - | MINIZINC OK |
| constraint_array2d_min_max_plain.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_array2d_min_max_plain.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_array2d_sum.mzn | base | base | - | MINIZINC OK |
| constraint_array2d_sum.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_min_max.mzn | base | base | - | MINIZINC OK |
| constraint_arrays_min_max.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_min_max.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | base | base | - | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 2 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 3 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 4 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 5 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 6 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 7 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 8 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_quantifiers.mzn | 9 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_sum.mzn | base | base | - | MINIZINC OK |
| constraint_arrays_sum.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_sum.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_sum.mzn | 2 | pos | PROVEN | MINIZINC OK |
| constraint_arrays_sum.mzn | 3 | pos | PROVEN | MINIZINC OK |
| constraint_bool2int.mzn | base | base | - | MINIZINC OK |
| constraint_bool2int.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_bool2int.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_bool_comparisons.mzn | base | base | - | MINIZINC OK |
| constraint_bool_comparisons.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_bool_comparisons.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_bool_set_literal.mzn | base | base | - | MINIZINC OK |
| constraint_bool_set_literal.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_bool_set_literal.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_circuit.mzn | base | base | - | MINIZINC OK |
| constraint_circuit.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_circuit.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_cumulative.mzn | base | base | - | MINIZINC OK |
| constraint_cumulative.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_cumulative.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_cumulative.mzn | 2 | pos | PROVEN | MINIZINC OK |
| constraint_cumulative.mzn | 3 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_cumulative_empty.mzn | base | base | - | MINIZINC OK |
| constraint_cumulative_empty.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_cumulative_empty.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_filtered_aggregators.mzn | base | base | - | MINIZINC OK |
| constraint_filtered_aggregators.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_filtered_aggregators.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_filtered_aggregators.mzn | 2 | pos | PROVEN | MINIZINC OK |
| constraint_filtered_aggregators.mzn | 3 | pos | PROVEN | MINIZINC OK |
| constraint_filtered_aggregators.mzn | 4 | pos | PROVEN | MINIZINC OK |
| constraint_filtered_aggregators.mzn | 5 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_int_comparisons.mzn | base | base | - | MINIZINC OK |
| constraint_int_comparisons.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_int_comparisons.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_let_admissibility.mzn | base | base | - | MINIZINC OK |
| constraint_let_admissibility.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_let_admissibility.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_let_admissibility.mzn | 2 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_let_in.mzn | base | base | - | MINIZINC OK |
| constraint_let_in.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_let_in_multi.mzn | base | base | - | MINIZINC OK |
| constraint_let_in_multi.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_let_in_multi.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_plain_aggregators.mzn | base | base | - | MINIZINC OK |
| constraint_plain_aggregators.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_plain_aggregators.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_plain_aggregators.mzn | 2 | pos | PROVEN | MINIZINC OK |
| constraint_plain_aggregators.mzn | 3 | neg | NOT VIOLATED | MINIZINC OK |
| constraint_set_ops_and_sets.mzn | base | base | - | MINIZINC OK |
| constraint_set_ops_and_sets.mzn | 0 | pos | PROVEN | MINIZINC OK |
| constraint_set_ops_and_sets.mzn | 1 | pos | PROVEN | MINIZINC OK |
| constraint_set_ops_and_sets.mzn | 2 | pos | PROVEN | MINIZINC OK |
| constraint_set_ops_and_sets.mzn | 3 | pos | PROVEN | MINIZINC OK |
| constraint_set_ops_and_sets.mzn | 4 | neg | NOT VIOLATED | MINIZINC OK |
| declarations_array.mzn | base | base | - | MINIZINC OK |
| declarations_array.mzn | 0 | pos | PROVEN | MINIZINC OK |
| declarations_array.mzn | 1 | pos | PROVEN | MINIZINC OK |
| declarations_array.mzn | 2 | pos | PROVEN | MINIZINC OK |
| declarations_array_comprehensions_and_sum.mzn | base | base | - | MINIZINC OK |
| declarations_array_comprehensions_and_sum.mzn | 0 | pos | PROVEN | MINIZINC OK |
| declarations_array_comprehensions_and_sum.mzn | 1 | pos | PROVEN | MINIZINC OK |
| declarations_array_of_sets.mzn | base | base | - | MINIZINC OK |
| declarations_array_of_sets.mzn | 0 | pos | PROVEN | MINIZINC OK |
| declarations_array_of_sets.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| declarations_array_unknown_length.mzn | base | base | - | MINIZINC OK |
| declarations_array_unknown_length.mzn | 0 | pos | PROVEN | MINIZINC OK |
| declarations_definitions.mzn | base | base | - | MINIZINC OK |
| declarations_definitions.mzn | 0 | pos | PROVEN | MINIZINC OK |
| declarations_definitions.mzn | 1 | neg | NOT VIOLATED | MINIZINC OK |
| declarations_ranges.mzn | base | base | - | MINIZINC OK |
| declarations_ranges.mzn | 0 | pos | PROVEN | MINIZINC OK |
| declarations_ranges.mzn | 1 | pos | PROVEN | MINIZINC OK |
| declarations_ranges.mzn | 2 | neg | NOT VIOLATED | MINIZINC OK |
| declarations_ranges.mzn | 3 | neg | NOT VIOLATED | MINIZINC OK |
| declarations_ranges.mzn | 4 | neg | NOT VIOLATED | MINIZINC OK |
| declarations_ranges.mzn | 5 | neg | NOT VIOLATED | MINIZINC OK |
| declarations_set_card.mzn | base | base | - | MINIZINC OK |
| declarations_set_card.mzn | 0 | pos | PROVEN | MINIZINC OK |
| declarations_unknown_index_and_domains.mzn | base | base | - | MINIZINC OK |
| declarations_unknown_index_and_domains.mzn | 0 | pos | PROVEN | MINIZINC OK |
| declarations_unknown_index_and_domains.mzn | 1 | pos | PROVEN | MINIZINC OK |
| declarations_unknown_index_and_domains.mzn | 2 | pos | PROVEN | MINIZINC OK |
| declarations_unknown_index_and_domains.mzn | 3 | pos | PROVEN | MINIZINC OK |
| declarations_unknown_index_and_domains.mzn | 4 | pos | PROVEN | MINIZINC OK |
| declarations_unknown_index_and_domains.mzn | 5 | neg | NOT VIOLATED | MINIZINC OK |
| functions_array1d_array2d.mzn | base | base | - | MINIZINC OK |
| functions_array1d_array2d.mzn | 0 | pos | PROVEN | MINIZINC OK |
| functions_array2d.mzn | base | base | - | MINIZINC OK |
| functions_array2d.mzn | 0 | pos | PROVEN | MINIZINC OK |
| functions_length_symmetry_and_array_eq.mzn | base | base | - | MINIZINC OK |
| functions_length_symmetry_and_array_eq.mzn | 0 | pos | PROVEN | MINIZINC OK |
| functions_length_symmetry_and_array_eq.mzn | 1 | pos | PROVEN | MINIZINC OK |
| functions_length_symmetry_and_array_eq.mzn | 2 | neg | NOT VIOLATED | MINIZINC OK |
| operators_arith_logic_functions.mzn | base | base | - | MINIZINC OK |
| operators_arith_logic_functions.mzn | 0 | pos | PROVEN | MINIZINC OK |
| operators_arith_logic_functions.mzn | 1 | pos | PROVEN | MINIZINC OK |
| operators_arith_logic_functions.mzn | 2 | neg | NOT VIOLATED | MINIZINC OK |
