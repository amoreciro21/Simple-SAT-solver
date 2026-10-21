#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

typedef struct Literal {
	int num;
	bool is_negated;
} Literal;

typedef struct Clause {
	int count;
	bool tautology;
	Literal literals[];
} Clause;

typedef struct Decision {
	int var_index;
	int next_value_to_try;
	int pos;
} Decision;

int count_words(char *s);

int my_compare(const void* a, const void* b); 

void string_array_sort(char **arr, int n);

int binary_search(char **a, int n, char *s);

Clause *parse_clause(char **var_names, int n, char *buff);

int get_bit(int val, int size, int id);

int assignment_check(unsigned int bits, int *trail, int n);

void apply_assignment(Clause **clauses, int n_clauses, int var, int val, int *num_true, int *num_unassigned, int *occurrence_counter, int **var_occurrence, int *conflict_count);

void undo_assignment(Clause **clauses, int n_clauses, int var, int val, int *num_true, int *num_unassigned, int *occurrence_counter, int **var_occurrence, int *conflict_count);

bool propagate(Clause **clauses, int n_clauses, int *assignment, int *num_true, int *num_unassigned, int *stack, int *stack_size, int *occurrence_counter, int **var_occurrence, int *conflict_count);

void undo_stack(Clause **clauses, int n_clauses, int *assignment, int *num_true, int *num_unassigned, int *stack, int *stack_size, int target_pos, int *occurrence_counter, int **var_occurrence, int *conflict_count);

int get_first_free_literal(int *arr, int n);

int get_best_free_literal(Clause **clauses, int n, int n_clauses, int *num_true, int *num_unassigned, int *assignment);

bool solver(Clause **clauses, int n, int n_clauses, int removed_count, int *num_true, int *num_unassigned, int *occurrence_counter, int **var_occurrence);

int main(int argc, char *argv[]) {

	#define MAXWORD 8192

	// Read the first line of the input (the list of variable names) and store it in a buffer.
	char buffer[MAXWORD];
	if (fgets(buffer, MAXWORD, stdin) == NULL) {
		printf("Error reading input\n");
		return 0;
	}

	// Count the number of variables and allocate an array of strings to hold their names.
	int n = count_words(buffer);
	char **var_names = malloc(n * sizeof(char *));

	int tk_index = 0;
	char *token = strtok(buffer, " \t\r\n");

	while (token != NULL && tk_index < n) {
		var_names[tk_index] = malloc(strlen(token) + 1);
		strcpy(var_names[tk_index], token);
		token = strtok(NULL, " \t\r\n");
		tk_index++;
	}

	// Sort the variable names alphabetically, so they can be looked up with binary search
	string_array_sort(var_names, n);

	// Remove duplicate variable names
	int u_n = 0;
	if (tk_index > 0) {
		u_n = 1;
		for (int i = 1; i < tk_index; i++) {
			if (strcmp(var_names[i], var_names[u_n - 1]) != 0) {
				var_names[u_n] = var_names[i];
				u_n++;
			} else {
				free(var_names[i]);
			}
		}
	}
	n = u_n;

	// Parse the remaining lines of the input: each line is a clause of the CNF formula
	int n_clauses = 0;
	int capacity = 100;
	Clause **c = malloc(sizeof(Clause *) * capacity);
	while (fgets(buffer, MAXWORD, stdin) != NULL) {
		if (n_clauses == capacity) {
			capacity *= 2;
			Clause **tmp = realloc(c, sizeof(Clause *) * capacity);
			if (tmp != NULL) {
				c = tmp;
			}
		}
		c[n_clauses] = parse_clause(var_names, n, buffer);
		n_clauses++;
	}	

	// For simplicity, initialize an integer matrix (array of arrays) that stores, for
	// each variable, the clauses it appears in. How do I distinguish negated from non-negated
	// occurrences? I add 1 to the clause index and flip its sign, so that clause 0
	// also has a negative counterpart.
	int *occ_count = calloc(n, sizeof(int));
	int **var_occurrence = malloc(n * sizeof(int *));

	for (int i = 0; i < n_clauses; i++) {
		for (int j = 0; j < c[i]->count; j++) {	
			occ_count[c[i]->literals[j].num]++;
		}
	}

	for (int i = 0; i < n; i++) {
		var_occurrence[i] = malloc(occ_count[i] * sizeof(int));
	}

	int *occ_counters = calloc(n, sizeof(int));
	for (int i = 0; i < n_clauses; i++) {
		for (int j = 0; j < c[i]->count; j++) {
			int x = c[i]->literals[j].num;
			bool neg = c[i]->literals[j].is_negated;
			var_occurrence[x][occ_counters[x]] = neg ? -(i + 1) : (i + 1);
			occ_counters[x]++; 
		}
	}

	free(occ_counters);

	// For each clause, keep track of the number of true literals under the current assignment
	// and the number of literals not yet assigned.

	int *num_true = malloc(n_clauses * sizeof(int));
	int *num_unassigned = malloc(n_clauses * sizeof(int));


	// If a set of clauses is satisfiable, then so is any subset of it. I use this property
	// to search for the number of clauses to remove: a binary-search-like strategy, so the number
	// of calls to solver() becomes O(log(n_clauses)) instead of O(n_clauses) in the worst case.
	int lower_limit = 0;
	int upper_limit = n_clauses;
	int mid_point;

	while (lower_limit < upper_limit) {
		mid_point = (lower_limit + upper_limit) / 2;
			int active_clauses = n_clauses - mid_point;
		if (solver(c, n, active_clauses, mid_point, num_true, num_unassigned, occ_count, var_occurrence)) {
			upper_limit = mid_point;
		} else {
			lower_limit = mid_point + 1;
		}
	}

	if (lower_limit == 0) {
		printf("SAT\n");
	} else {
		printf("UNSAT\n");
		for (int i = 1; i <= upper_limit; i++) {
			printf("-%d\n", i);
		}
		printf("SAT\n");
	}

	// Free memory
	for (int i = 0; i < n; i++) {
    	free(var_names[i]);
	}

	for (int i = 0; i < n_clauses; i++) {
    	free(c[i]);
	}

	for (int i = 0; i < n; i++) {
    free(var_occurrence[i]);
	}

	free(var_occurrence);
	free(occ_count);
	free(num_true);
	free(num_unassigned);
	free(var_names);
	free(c);
	return 0;
}


// Counts the number of words in a string
int count_words(char *s) {
	int n_words = 0;
	int i = 0;
	bool sawWord = false;
	while (s[i] != '\0' && s[i] != '\n') {
		if (s[i] == ' ' || s[i] == '\t' || s[i] == '\r') {
			sawWord = false;
		} else if (!sawWord){
			n_words++;
			sawWord = true;
		}
		i++;
	}
	return n_words;
}

// Comparator used to sort an array of strings.
int my_compare(const void* a, const void* b) 
{ 
    return strcmp(*(const char**)a, *(const char**)b); 
} 

// Helper function to sort an array of strings alphabetically with qsort().
void string_array_sort(char **arr, int n) 
{ 
    qsort(arr, n, sizeof(char*), my_compare); 
}

// Binary search for a string in an alphabetically sorted array of strings.
int binary_search(char **a, int n, char *s) {
	int l = 0;
	int r = n - 1;
	int m, cmp;

	while (l <= r) {
		m = l + (r - l) / 2;
		cmp = strcmp(a[m], s);
		if (cmp < 0) {
			l = m + 1;
		} else if (cmp > 0) {
			r = m - 1;
		} else {
			return m;
		}
	}
	return -1;
}

// Parses a clause from a line of text. Each token is a variable name, optionally
// prefixed with '-' for negation. Unknown names and duplicate literals are ignored,
// and a clause containing both x and -x is marked as a tautology.
Clause *parse_clause(char **var_names, int n, char *buff) {
	int tk_index = 0;
	int pos;
	bool is_neg, is_dup;
	int max_literals = count_words(buff);
	char *token = strtok(buff, " \t\r\n");
	Clause *c = malloc(sizeof(Clause) + (max_literals * sizeof(Literal)));
	c->count = 0;
	c->tautology = false;

	while (token != NULL && tk_index < n) {
		is_neg = (token[0] == '-');
		is_dup = false;
		char *var_name = is_neg ? token + 1 : token;
		pos = binary_search(var_names, n, var_name);

		if (pos != -1) {
			for (int i = 0; i < c->count; i++) {
				if (c->literals[i].num == pos) {
					if (c->literals[i].is_negated != is_neg) {
						c->tautology = true;
						is_dup = true;
					} else {
						is_dup = true;
					}
				}
			}

			if (!is_dup) {	
				c->literals[c->count].num = pos;
				c->literals[c->count].is_negated = is_neg;
				c->count++;
				tk_index++;
			}
		token = strtok(NULL, " \t\r\n");
		}
	}

	return c;
}

// Returns the bit at position id of the binary representation of val
int get_bit(int val, int size, int id) {
    return (val >> (size - 1 - id)) & 1;
}

void apply_assignment(Clause **clauses, int n_clauses, int var, int val, int *num_true, int *num_unassigned, int *occurrence_counter, int **var_occurrence, int *conflict_count) {

	for (int i = 0; i < occurrence_counter[var]; i++) {
		int curr_clause = (var_occurrence[var][i] < 0) ? (-var_occurrence[var][i] - 1) : (var_occurrence[var][i] - 1);  
		bool is_neg = (var_occurrence[var][i] < 0) ? true : false;

		if (curr_clause < n_clauses) {
			num_unassigned[curr_clause]--;
			if (!is_neg && val == 1) {
				num_true[curr_clause]++;
			} else if (is_neg && val == 0) {
				num_true[curr_clause]++;
			}

			if (num_true[curr_clause] == 0 && num_unassigned[curr_clause] == 0) {
				(*conflict_count)++;
			}
		}
	}
}

void undo_assignment(Clause **clauses, int n_clauses, int var, int val, int *num_true, int *num_unassigned, int *occurrence_counter, int **var_occurrence, int *conflict_count) {

	for (int i = 0; i < occurrence_counter[var]; i++) {
		int curr_clause = (var_occurrence[var][i] < 0) ? (-var_occurrence[var][i] - 1) : (var_occurrence[var][i] - 1);  

		if (curr_clause < n_clauses) {
			bool is_neg = (var_occurrence[var][i] < 0) ? true : false;

			if (num_true[curr_clause] == 0 && num_unassigned[curr_clause] == 0) {
				(*conflict_count)--;
			}

			num_unassigned[curr_clause]++;
			if (!is_neg && val == 1) {
				num_true[curr_clause]--;
			} else if (is_neg && val == 0) {
				num_true[curr_clause]--;
			}
		}

	}
}

bool propagate(Clause **clauses, int n_clauses, int *assignment, int *num_true, int *num_unassigned, int *stack, int *stack_size, int *occurrence_counter, int **var_occurrence, int *conflict_count) {
	if (*conflict_count > 0) {
		return false;
	}
	bool changed = true;
	while (changed) {
		changed = false;
		for (int i = 0; i < n_clauses; i++) {
			if (!clauses[i]->tautology && num_true[i] == 0 && num_unassigned[i] == 1) {
				for (int j = 0; j < clauses[i]->count; j++) {
					int var = clauses[i]->literals[j].num;
					if (assignment[var] == -1) {
						int val = clauses[i]->literals[j].is_negated ? 0 : 1;
						assignment[var] = val;
						apply_assignment(clauses, n_clauses, var, val, num_true, num_unassigned, occurrence_counter, var_occurrence, conflict_count);
						stack[(*stack_size)++] = var;
						changed = true;
						break;
					}
				}
				if (*conflict_count > 0) {
					return false;
				}
			}
		}
	}
	return true;

}

void undo_stack(Clause **clauses, int n_clauses, int *assignment, int *num_true, int *num_unassigned, int *stack, int *stack_size, int target_pos, int *occurrence_counter, int **var_occurrence, int *conflict_count) {
	while (*stack_size > target_pos) {
		int var = stack[--(*stack_size)];
		int val = assignment[var];
		assignment[var] = -1;
		undo_assignment(clauses, n_clauses, var, val, num_true, num_unassigned, occurrence_counter, var_occurrence, conflict_count);
	}
}

// Returns the first variable that has not been assigned yet
int get_first_free_literal(int *arr, int n) {
	for (int i = 0; i < n; i++) {
		if (arr[i] == -1) {
			return i;
		}
	}
	return -1;
}

// Finds the not-yet-satisfied clause with the fewest unassigned literals
// and returns one of its unassigned variables
int get_best_free_literal(Clause **clauses, int n, int n_clauses, int *num_true, int *num_unassigned, int *assignment) {
	int best_clause = -1;
	int best_size = n + 1;

	for (int i = 0; i < n_clauses; i++) {
		if (num_true[i] == 0 && num_unassigned[i] > 0) {
			if (num_unassigned[i] < best_size) {
				best_size = num_unassigned[i];
				best_clause = i;
			}
		} 
	}

	if (best_clause != -1) {
		for (int j = 0; j < clauses[best_clause]->count; j++) {
			if (assignment[clauses[best_clause]->literals[j].num] == -1) {
				return clauses[best_clause]->literals[j].num;
			}
 		}
	}

	return get_first_free_literal(assignment, n);
}

bool solver(Clause **clauses, int n, int n_clauses, int removed_count, int *num_true, int *num_unassigned, int *occurrence_counter, int **var_occurrence) {

	// The empty formula is true
	if (n_clauses == 0) {
		return true;
	}

	// Initialize the partial assignment array
	int *assignment = malloc(n * sizeof(int));
	for (int i = 0; i < n; i++) {
    	assignment[i] = -1;
	}

	// Find all clauses with a single literal. The assignment must necessarily satisfy them.
	// If a contradiction is found at this point, the formula is unsatisfiable.
	for (int i = 0; i < n_clauses; i++) {
		if (clauses[i]->count == 1 && !clauses[i]->tautology) {
			int curr = clauses[i]->literals[0].num;
			bool is_negated = clauses[i]->literals[0].is_negated;

			if ((assignment[curr] == 0 && !is_negated) || (assignment[curr] == 1 && is_negated)) {
				free(assignment);
				return false;
			} else {
				assignment[curr] = is_negated ? 0 : 1;
			}
		}
	}

	// Further refine the partial assignment: if a variable appears only negated or only non-negated
	// across all clauses, assign it (1 if non-negated, 0 otherwise). I use 2 to mark variables
	// that appear both negated and non-negated (these obviously shouldn't be assigned yet).
	int *literal_filter = malloc(n * sizeof(int));
	for (int i = 0; i < n; i++) {
		literal_filter[i] = -1;
	}

	for (int i = 0; i < n_clauses; i++) {
		if (clauses[i]->count > 1 && !clauses[i]->tautology) {
			for (int j = 0; j < clauses[i]->count; j++) {
				int curr = clauses[i]->literals[j].num;
				bool is_negated = clauses[i]->literals[j].is_negated;

				if (literal_filter[curr] == -1) {
					literal_filter[curr] = is_negated ? 0 : 1;
				} else if (literal_filter[curr] == 1 && is_negated) {
					literal_filter[curr] = 2;
				} else if (literal_filter[curr] == 0 && !is_negated) {
					literal_filter[curr] = 2;
				}
			}
		}
	}

	for (int i = 0; i < n; i++) {
		if (literal_filter[i] == 1 || literal_filter[i] == 0) {
			if (assignment[i] == -1) {
				assignment[i] = literal_filter[i];
			}
		}
	}

	free(literal_filter);

	// Initialize num_true and num_unassigned.
	for (int i = 0; i < n_clauses; i++) {
		num_true[i] = 0;
		num_unassigned[i] = 0;
		if (clauses[i]->tautology) {
			num_true[i] = 1;
			num_unassigned[i] = 0;
		}
		for (int j = 0; j < clauses[i]->count; j++) {
			int val = clauses[i]->literals[j].num;
			if (assignment[val] == 1 && !clauses[i]->literals[j].is_negated) {
				num_true[i]++;
			} else if (assignment[val] == 0 && clauses[i]->literals[j].is_negated) {
				num_true[i]++;
			} else if (assignment[val] == -1) {
				num_unassigned[i]++;
			}
		}
	}

	Decision *decisions = malloc(n * sizeof(Decision));
	int *stack = malloc(n * sizeof(int));
	int stack_size = 0;
	int d_index = 0;
	bool sat = false;
	bool unsat = false;
	int conflict_count = 0;

	for (int i = 0; i < n_clauses; i++) {
    	if (num_true[i] == 0 && num_unassigned[i] == 0) {
        	conflict_count++;
    	}
    }

	bool conflict =  !propagate(clauses, n_clauses, assignment, num_true, num_unassigned, stack, &stack_size, occurrence_counter, var_occurrence, &conflict_count);

	while (!sat && !unsat) {
		if (!conflict) {
			int var = get_best_free_literal(clauses, n, n_clauses, num_true, num_unassigned, assignment);

			if (var == -1) {
				sat = true;
			} else {
				int stack_pos_before = stack_size;
				assignment[var] = 1;
				apply_assignment(clauses, n_clauses, var, 1, num_true, num_unassigned, occurrence_counter, var_occurrence, &conflict_count);

				stack[stack_size++] = var;

				decisions[d_index].var_index = var;
				decisions[d_index].next_value_to_try = 0;
				decisions[d_index].pos = stack_pos_before;
				d_index++;

				conflict = !propagate(clauses, n_clauses, assignment, num_true, num_unassigned, stack, &stack_size, occurrence_counter, var_occurrence, &conflict_count);
			}
		} else {
			if (d_index == 0) {
				unsat = true;
			} else {
				Decision *top = &decisions[d_index - 1];
				undo_stack(clauses, n_clauses, assignment, num_true, num_unassigned, stack, &stack_size, top->pos, occurrence_counter, var_occurrence, &conflict_count);

				if (top->next_value_to_try != -1) {
					int retry_val = top->next_value_to_try;
					top->next_value_to_try = -1;

					assignment[top->var_index] = retry_val;
					apply_assignment(clauses, n_clauses, top->var_index, retry_val, num_true, num_unassigned, occurrence_counter, var_occurrence, &conflict_count);

					stack[stack_size++] = top->var_index;

					conflict = !propagate(clauses, n_clauses, assignment, num_true, num_unassigned, stack, &stack_size, occurrence_counter, var_occurrence, &conflict_count);
				} else {
					d_index--;
				}
			}
		}
	}

	free(stack);
	free(decisions);
	free(assignment);

	return sat;
}