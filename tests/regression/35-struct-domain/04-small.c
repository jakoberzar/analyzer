#include "assert.h"
#include "stdio.h"

struct FunctionInfo {
    void* ptr;
    int id;
};

struct FunctionInfo functionToRun;

/// Finds the factorial of given number
int factorial(int n) {
    if (n <= 1) {
        printf("End of recursion reached!\n"); // create a side effect and prevent optimizations
        return 1;
    }
    return n * factorial(n - 1);
}

/// Finds the "n" given a "n!".
/// In case an integer "n" cannot be calculated, return the upper (ceil) number.
int inverseFactorial(int fac) {
    int product = 1;
    int n = 1;
    while (product < fac) {
        n++;
        product *= n;
    }
    printf("Inverse found!\n"); // create a side effect and prevent optimizations
    return n;
}


int main() {
    int n;
    int choice;
    int test;

    // functionToRun.id = 1;
    // functionToRun.ptr = factorial;
    // test = 1;
    if (choice == 1) {
        functionToRun.id = 1;
        functionToRun.ptr = factorial;
        test = 1;
    } else {
        functionToRun.id = 2;
        functionToRun.ptr = inverseFactorial;
        test = 2;
    }

    typedef int (*fun)(int);
    if (functionToRun.id == 1) {
    // if (strcmp(functionToRun.name, "factorial") == 0) {
        fun f = functionToRun.ptr;
        assert(f == factorial);
        int result = f(n);
        printf("Factorial of %d is %d\n", n, result);
    } else if (functionToRun.id == 2) {
    // } else if (strcmp(functionToRun.name, "inverse factorial") == 0) {
        fun f = functionToRun.ptr;
        assert(f == inverseFactorial);
        int result = f(n);
        printf("Factorial of %d is %d\n", result, n);
    } else {
        fun f = functionToRun.ptr;
        printf("Exiting with code %d...\n", n);
        int result = f(n);
    }

    return 0;
}
