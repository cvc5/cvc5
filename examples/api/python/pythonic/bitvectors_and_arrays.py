from cvc5.pythonic import *

if __name__ == '__main__':
    # Consider the following (where k is some previously defined constant):
    #
    #
    #   Assert (current_array[0] > 0);
    #   for (unsigned i = 1; i < k; ++i) {
    #     current_array[i] = 2 * current_array[i - 1];
    #     Assert (current_array[i-1] < current_array[i]);
    #   }
    #
    # We want to check whether the assertion in the body of the for loop holds
    # throughout the loop.
    k = 4
    idx_bits = int(math.ceil(math.log(k, 2)))

    init_array = Array('init_arr', BitVecSort(idx_bits), BitVecSort(32))
    array = init_array
    assertions = []
    for i in range(1, k):
        array = Store(array, i, 2 * Select(array, i - 1))
        assertions.append(Select(array, i - 1) < Select(array, i))
    # Does *not* hold.
    # If the first element is large enough, the multiplication overflows.
    prove(Implies(Select(init_array, 0) > 0, And(*assertions)))
